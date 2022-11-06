#![no_std]
#![deny(clippy::alloc_instead_of_core)]
#![deny(clippy::allow_attributes_without_reason)]
// TODO: enable this when clippy hits 1.66.0
// #![deny(clippy::as_ptr_cast_mut)]
#![deny(clippy::cast_possible_truncation)]
#![deny(clippy::dbg_macro)]
#![deny(clippy::equatable_if_let)]
#![deny(clippy::filter_map_next)]
#![deny(clippy::flat_map_option)]
// denied to ensure there's no casual regular arithmetic that may panic, can be sparingly allowed
// for situations where a comment explains why it is safe
#![deny(clippy::integer_arithmetic)]
#![deny(clippy::map_unwrap_or)]
// TODO: uncomment after todo!()'s are removed
// #![deny(clippy::missing_panics_doc)]
#![deny(clippy::option_if_let_else)]
#![deny(clippy::panic)]
#![deny(clippy::std_instead_of_alloc)]
#![deny(clippy::std_instead_of_core)]
// TODO: uncomment after todo!()'s are removed
// #![deny(clippy::todo)]
#![deny(clippy::wildcard_enum_match_arm)]
#![deny(clippy::wildcard_imports)]
#![deny(macro_use_extern_crate)]
// TODO: enable this when things are stable
// #![deny(missing_docs)]
// TODO: fix the false-positive here with js-sys and wasm-bindgen
// #![deny(unused_crate_dependencies)]
#![deny(unused_extern_crates)]
#![deny(unused_lifetimes)]
#![deny(unused_qualifications)]

use parsnips_util::IndexAligned;
#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
pub struct Emulator {
    gprs: [u32; 32],
    pc: u32,
    unpredictable: bool,
}

static mut GARBAGE: u32 = 0;

#[cfg_attr(target_arch = "wasm32", wasm_bindgen)]
impl Emulator {
    #[allow(clippy::new_without_default)]
    #[cfg_attr(target_arch = "wasm32", wasm_bindgen(constructor))]
    pub fn new() -> Self {
        Self {
            gprs: [0; 32],
            pc: 0,
            unpredictable: false,
        }
    }

    // NOTE: step must take memory as parameter instead of it being provided it to Emulator::new
    // because wasm_bindgen values cannot have lifetimes
    // TODO: figure out how to fix this, even if it means dropping wasm_bindgen and making the js
    // bindings unsafe

    /// Retrieve a mutable reference to the general purose register index, unless index == 0, in
    /// which case this function returns a mutable reference to a value that will never be read.
    ///
    /// This is consistent with the definition of $zero in table 1.2 of the spec, where it
    /// indicates that non-zero writes should be ignored.
    fn gpr_mut(&mut self, index: usize) -> &mut u32 {
        if index == 0 {
            // TODO: figure out how to express this clearly without this kind of hack, and without
            // having to use some kind of annoying set_gpr() method
            return unsafe { &mut GARBAGE };
        }
        &mut self.gprs[index]
    }

    pub fn step(&mut self, memory: &mut [u8]) {
        // TODO: is there any way I can require this through types?
        assert_eq!(memory.len() % 4, 0);

        use parsnips_util::inst::{self, Opcode};

        if self.pc as usize >= memory.len() {
            todo!();
        }
        let inst: inst::Inst = if self.pc % 4 == 0 {
            unsafe { memory.index_aligned(self.pc as usize) }
        } else {
            todo!();
        };

        // this is safe because if self.pc < memory.len() and both self.pc and memory.len() have
        // % 4 == 0 then self.pc <= memory.len() - 4 for big self.pc, meaning that
        // self.pc + 4 <= memory.len() so self.pc + 4 <= u32::MAX since memory.len() <= usize::MAX
        // and u32::MAX <= usize::MAX for all suported architectures
        // TODO: vet what architectures the final condition is false on and find a way to mark them
        // as unsupported, since dealing with that condition will be very challenging
        #[allow(clippy::integer_arithmetic)]
        {
            self.pc += 4;
        }

        match if let Some(opcode) = inst::InstFields::opcode(&inst) {
            opcode
        } else {
            return todo!();
        } {
            Opcode::SPECIAL => {
                use inst::special::{Special, SpecialFields};

                match if let Some(function) = inst.function() {
                    function
                } else {
                    return todo!();
                } {
                    Special::SLL => {
                        if inst.rs() == 0 && inst.rt() == 0 && inst.rd() == 0 {
                            #[allow(clippy::wildcard_in_or_patterns)]
                            match inst.sa() {
                                3 => return todo!(), // EHB
                                5 => return todo!(), // PAUSE
                                0 /* NOP */ | _ /* not something else, continue to SHL */ => {}
                            }
                        }

                        // shl only panics for rhs > u32::BITS, so this is safe since:
                        // bit_width(inst.sa()) <= 5 <=> inst.sa() <= 32 == u32::BITS
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) = self.gprs[inst.rt()] << inst.sa();
                        }
                    }
                    Special::SRL => {
                        match inst.rd() {
                            0 /* SRL */ => {},
                            1 /* ROTR */ => {
                                *self.gpr_mut(inst.rd()) =
                                    self.gprs[inst.rt()].rotate_right(inst.sa());
                                return;
                            },
                            _ => self.unpredictable = true,
                        }

                        // safe by the same justification as SLL
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) = self.gprs[inst.rt()] >> inst.sa();
                        }
                    }
                    Special::SRA => {
                        if inst.rs() != 0 {
                            self.unpredictable = true;
                        }

                        // safe by the same justification as SLL
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) =
                                ((self.gprs[inst.rt()] as i32) >> inst.sa()) as u32;
                        }
                    }
                    Special::SLLV => {
                        if inst.sa() != 0 {
                            self.unpredictable = true;
                        }

                        // safe by similar justification to SLL, since rhs is determined by the 5
                        // least-significant bits of $rs
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) =
                                self.gprs[inst.rt()] << (self.gprs[inst.rs()] & 0b11111);
                        }
                    }
                    Special::LSA => {
                        if inst.sa() & 0b11100 != 0 {
                            self.unpredictable = true;
                        }

                        // safe by similar justification to SLL, since:
                        // (inst.sa() | 0b11) + 1 <= 5 < 32 == u32::BITS
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) = (self.gprs[inst.rs()]
                                << ((inst.sa() | 0b11) + 1))
                                + self.gprs[inst.rt()];
                        }
                    }
                    Special::SRLV => {
                        match inst.sa() {
                            0 /* SRLV */ => {}
                            1 /* ROTRV */ => {
                                *self.gpr_mut(inst.rd()) = self.gprs[inst.rt()]
                                        .rotate_right(self.gprs[inst.rs()] & 0b11111);
                                return;
                            }
                            _ => self.unpredictable = true,
                        }

                        // safe by the same justification as SLLV
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) =
                                self.gprs[inst.rt()] >> (self.gprs[inst.rs()] & 0b11111);
                        }
                    }
                    Special::SRAV => {
                        if inst.sa() != 0 {
                            self.unpredictable = true;
                        }

                        // safe by the same justification as SLLV
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) = ((self.gprs[inst.rt()] as i32)
                                >> (self.gprs[inst.rs()] & 0b11111))
                                as u32;
                        }
                    }
                    Special::JALR => todo!(), // TODO: JALR.HB
                    Special::SYSCALL => todo!(),
                    Special::BREAK => todo!(),
                    Special::SDBBP => todo!(),
                    Special::SYNC => todo!(),
                    Special::CLZ => todo!(),
                    Special::CLO => todo!(),
                    Special::SOP30 => todo!(),
                    Special::SOP31 => todo!(),
                    Special::SOP32 => todo!(),
                    Special::SOP33 => todo!(),
                    Special::ADD => todo!(),
                    Special::ADDU => todo!(),
                    Special::SUB => todo!(),
                    Special::SUBU => todo!(),
                    Special::AND => todo!(),
                    Special::OR => todo!(),
                    Special::XOR => todo!(),
                    Special::NOR => todo!(),
                    Special::SLT => todo!(),
                    Special::SLTU => todo!(),
                    Special::TGE => todo!(),
                    Special::TGEU => todo!(),
                    Special::TLT => todo!(),
                    Special::TLTU => todo!(),
                    Special::TEQ => todo!(),
                    Special::SELEQZ => todo!(),
                    Special::TNE => todo!(),
                    Special::SELNEZ => todo!(),
                };
            }
            Opcode::REGIMM => {
                use inst::regimm::{self, Regimm};

                match if let Some(rt) = regimm::RegimmFields::rt(&inst) {
                    rt
                } else {
                    return todo!();
                } {
                    Regimm::BLTZ => todo!(),
                    Regimm::BGEZ => todo!(),
                    Regimm::DAHI => todo!(),
                    Regimm::NAL => todo!(),
                    Regimm::BAL => todo!(),
                    Regimm::SIGRIE => todo!(),
                    Regimm::DATI => todo!(),
                    Regimm::SYNCI => todo!(),
                }
            }
            Opcode::J => todo!(),
            Opcode::JAL => todo!(),
            Opcode::BEQ => todo!(),
            Opcode::BNE => todo!(),
            Opcode::POP06 => todo!(), // TODO: BLEZ, BGEZALC, BLEZALC, BGEUC
            Opcode::POP07 => todo!(), // TODO: BGTZ, BLTZALC, BGTZALC, BLTUC
            Opcode::POP10 => todo!(), // TODO: BEQZALC, BEQC, BOVC
            Opcode::ADDIU => todo!(),
            Opcode::SLTI => todo!(),
            Opcode::SLTIU => todo!(),
            Opcode::ANDI => todo!(),
            Opcode::ORI => todo!(),
            Opcode::XORI => todo!(),
            Opcode::AUI => todo!(), // TODO: LUI
            Opcode::COP0 => todo!(),
            Opcode::COP1 => todo!(),
            Opcode::COP2 => todo!(),
            Opcode::POP26 => todo!(), // TODO: BGEZC, BLEZC, BGEC
            Opcode::POP27 => todo!(), // TODO: BLTZC, BGTZC, BLTC
            Opcode::POP30 => todo!(), // TODO: BNEZALC, BNEC, BNVC
            Opcode::MSA => todo!(),
            Opcode::SPECIAL3 => {
                use inst::special3::{self, Special3};

                match if let Some(function) = special3::Special3Fields::function(&inst) {
                    function
                } else {
                    return todo!();
                } {
                    Special3::EXT => todo!(),
                    Special3::INS => todo!(),
                    Special3::CRC => todo!(), // TODO: CRC32B, CRC32H, CRC32W, CRC32CB, CRC32CH, CRC32CW
                    Special3::CACHEE => todo!(),
                    Special3::SBE => todo!(),
                    Special3::SHE => todo!(), // TODO: SCWPE
                    Special3::SCE => todo!(),
                    Special3::SWE => todo!(),
                    Special3::BSHFL => todo!(), // TODO: ALIGN, BITSWAP, SEB, SEH, WSBH
                    Special3::PREFE => todo!(),
                    Special3::CACHE => todo!(),
                    Special3::SC => todo!(), // TODO: SCWP
                    Special3::LBUE => todo!(),
                    Special3::LHUE => todo!(),
                    Special3::LBE => todo!(),
                    Special3::LHE => todo!(),
                    Special3::LLE => todo!(), // TODO: LLPWE
                    Special3::LWE => todo!(),
                    Special3::PREF => todo!(),
                    Special3::LL => todo!(), // TODO: LLPW
                    Special3::RDHWR => todo!(),
                    Special3::GINV => todo!(), // TODO: GINVI, GINVT
                }
            }
            Opcode::LB => todo!(),
            Opcode::LH => todo!(),
            Opcode::LW => todo!(),
            Opcode::LBU => todo!(),
            Opcode::LHU => todo!(),
            Opcode::SB => todo!(),
            Opcode::SH => todo!(),
            Opcode::SW => todo!(),
            Opcode::CACHE => todo!(),
            Opcode::LL => todo!(),
            Opcode::LWC1 => todo!(),
            Opcode::BC => todo!(),
            Opcode::PREF => todo!(),
            Opcode::LDC1 => todo!(),
            Opcode::POP66 => todo!(), // TODO: ADDIUPC, LWPC, LWUPC, LDPC, AUIPC
            Opcode::SC => todo!(),
            Opcode::SWC1 => todo!(),
            Opcode::BALC => todo!(),
            Opcode::PCREL => todo!(),
            Opcode::SDC1 => todo!(),
            Opcode::POP76 => todo!(), // TODO: BNEZC, JIALC
        };
    }
}
