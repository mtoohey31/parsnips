#![no_std]
#![deny(
    clippy::alloc_instead_of_core,
    clippy::allow_attributes_without_reason,
    // TODO: enable this when clippy hits 1.66.0
    // clippy::as_ptr_cast_mut,
    clippy::cast_possible_truncation,
    clippy::dbg_macro,
    clippy::equatable_if_let,
    clippy::filter_map_next,
    clippy::flat_map_option,
    // denied to ensure there's no casual regular arithmetic that may panic, can be sparingly
    // allowed for situations where a comment explains why it is safe
    clippy::integer_arithmetic,
    clippy::map_unwrap_or,
    // TODO: uncomment after todo!()'s are removed
    // clippy::missing_panics_doc,
    clippy::option_if_let_else,
    clippy::panic,
    clippy::std_instead_of_alloc,
    clippy::std_instead_of_core,
    // TODO: uncomment after todo!()'s are removed
    // clippy::todo,
    clippy::wildcard_enum_match_arm,
    clippy::wildcard_imports,
    macro_use_extern_crate,
    // TODO: enable this when things are stable
    // missing_docs,
    // TODO: fix the false-positive here with js-sys and wasm-bindgen
    // unused_crate_dependencies,
    unused_extern_crates,
    unused_lifetimes,
    unused_qualifications,
)]

use arbitrary_int::u5;
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

    fn gpr(&self, index: u5) -> u32 {
        self.gprs[index.value() as usize]
    }

    /// Retrieve a mutable reference to the general purose register index, unless index == 0, in
    /// which case this function returns a mutable reference to a value that will never be read.
    ///
    /// This is consistent with the definition of $zero in vol II-A table 1.2 of the spec, where it
    /// indicates that non-zero writes should be ignored.
    fn gpr_mut(&mut self, index: u5) -> &mut u32 {
        let index = index.value() as usize;
        if index == 0 {
            // TODO: figure out how to express this clearly without this kind of hack, and without
            // having to use some kind of annoying set_gpr() method
            return unsafe { &mut GARBAGE };
        }
        &mut self.gprs[index]
    }

    // NOTE: step must take memory as parameter instead of it being provided it to Emulator::new
    // because wasm_bindgen values cannot have lifetimes
    // TODO: figure out how to fix this, even if it means dropping wasm_bindgen and making the js
    // bindings unsafe

    pub fn step(&mut self, memory: &mut [u8]) {
        // TODO: is there any way I can require this through types?
        assert_eq!(memory.len() % 4, 0);

        use parsnips_util::inst::{self, Opcode};

        if self.pc as usize >= memory.len() {
            todo!();
        }
        let inst = if self.pc % 4 == 0 {
            inst::Inst::new_with_raw_value(unsafe { memory.index_aligned(self.pc as usize) })
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

        match match inst.opcode() {
            Ok(opcode) => opcode,
            Err(_) => return todo!(),
        } {
            Opcode::SPECIAL => {
                // TODO: investigate if we can enforce that fields only get used once in here
                // somehow... because bugs resulting from mistaking one register for another seem
                // very likely...
                use inst::special::Special;
                let inst = inst::RInst::new_with_raw_value(inst.raw_value());

                match match inst.function() {
                    Ok(function) => function,
                    Err(_) => return todo!(),
                } {
                    Special::SLL => {
                        if inst.rs().value() == 0
                            && inst.rt().value() == 0
                            && inst.rd().value() == 0
                        {
                            #[allow(clippy::wildcard_in_or_patterns)]
                            match inst.sa().value() {
                                // TODO: move these hard-coded constants, as well as similar
                                // constants further down, into the util crate
                                // EHB
                                3 => return todo!(),
                                // PAUSE
                                5 => return todo!(),
                                // NOP, or not something else, so continue to SHL
                                0 | _ => {}
                            }
                        }

                        // shl only panics for rhs > u32::BITS, so this is safe since:
                        // bit_width(inst.sa()) <= 5 <=> inst.sa() <= 32 == u32::BITS
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) = self.gpr(inst.rt()) << inst.sa().value();
                        }
                    }
                    Special::SRL => {
                        match inst.rd().value() {
                            // SRL
                            0 => {}
                            // ROTR
                            1 => {
                                *self.gpr_mut(inst.rd()) =
                                    self.gpr(inst.rt()).rotate_right(inst.sa().value() as u32);
                                return;
                            }
                            _ => self.unpredictable = true,
                        }

                        // safe by the same justification as SLL
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) = self.gpr(inst.rt()) >> inst.sa().value();
                        }
                    }
                    Special::SRA => {
                        if inst.rs().value() != 0 {
                            self.unpredictable = true;
                        }

                        // safe by the same justification as SLL
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) =
                                ((self.gpr(inst.rt()) as i32) >> inst.sa().value()) as u32;
                        }
                    }
                    Special::SLLV => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        // safe by similar justification to SLL, since rhs is determined by the 5
                        // least-significant bits of $rs
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) =
                                self.gpr(inst.rt()) << (self.gpr(inst.rs()) & 0b11111);
                        }
                    }
                    Special::LSA => {
                        if inst.sa().value() & 0b11100 != 0 {
                            self.unpredictable = true;
                        }

                        // safe by similar justification to SLL, since:
                        // (inst.sa() | 0b11) + 1 <= 5 < 32 == u32::BITS
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) = (self.gpr(inst.rs())
                                << ((inst.sa().value() | 0b11) + 1))
                                + self.gpr(inst.rt());
                        }
                    }
                    Special::SRLV => {
                        match inst.sa().value() {
                            // SRLV
                            0 => {}
                            // ROTRV
                            1 => {
                                *self.gpr_mut(inst.rd()) = self
                                    .gpr(inst.rt())
                                    .rotate_right(self.gpr(inst.rs()) & 0b11111);
                                return;
                            }
                            _ => self.unpredictable = true,
                        }

                        // safe by the same justification as SLLV
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) =
                                self.gpr(inst.rt()) >> (self.gpr(inst.rs()) & 0b11111);
                        }
                    }
                    Special::SRAV => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        // safe by the same justification as SLLV
                        #[allow(clippy::integer_arithmetic)]
                        {
                            *self.gpr_mut(inst.rd()) = ((self.gpr(inst.rt()) as i32)
                                >> (self.gpr(inst.rs()) & 0b11111))
                                as u32;
                        }
                    }
                    Special::JALR => todo!(), // TODO: JALR.HB
                    Special::SYSCALL => todo!(),
                    Special::BREAK => todo!(),
                    Special::SDBBP => todo!(),
                    Special::SYNC => todo!(),
                    Special::CLZ => {
                        if inst.rt().value() != 0 || inst.sa().value() != 1 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = self.gpr(inst.rs()).leading_zeros();
                    }
                    Special::CLO => {
                        if inst.rt().value() != 0 || inst.sa().value() != 1 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = self.gpr(inst.rs()).leading_ones();
                    }
                    Special::SOP30 => match inst.sa().value() {
                        // MUL
                        0b00010 => {
                            // this is safe because i32::MAX * i32::MAX < i64::MAX, and we &
                            // for just the lower bits before we convert back to u32
                            #[allow(clippy::integer_arithmetic)]
                            {
                                let full = (self.gpr(inst.rs()) as i32 as i64)
                                    * (self.gpr(inst.rt()) as i32 as i64);
                                *self.gpr_mut(inst.rd()) = (full as u64 & ((1 << 32) - 1)) as u32;
                            }
                        }
                        // MUH
                        0b00011 => {
                            // same as above, but wit the upper bits instead this time
                            #[allow(clippy::integer_arithmetic)]
                            {
                                let full = (self.gpr(inst.rs()) as i32 as i64)
                                    * (self.gpr(inst.rt()) as i32 as i64);
                                *self.gpr_mut(inst.rd()) = (full as u64 >> 32) as u32;
                            }
                        }
                        _ => todo!(), // raise reserved
                    },
                    Special::SOP31 => match inst.sa().value() {
                        // MULU
                        0b00010 => {
                            // this is safe because u32::MAX * u32::MAX < u64::MAX, and we &
                            // for just the lower bits before we convert back to u32
                            #[allow(clippy::integer_arithmetic)]
                            {
                                let full =
                                    (self.gpr(inst.rs()) as u64) * (self.gpr(inst.rt()) as u64);
                                *self.gpr_mut(inst.rd()) = (full & ((1 << 32) - 1)) as u32;
                            }
                        }
                        // MUHU
                        0b00011 => {
                            // same as above, but wit the upper bits instead this time
                            #[allow(clippy::integer_arithmetic)]
                            {
                                let full =
                                    (self.gpr(inst.rs()) as u64) * (self.gpr(inst.rt()) as u64);
                                *self.gpr_mut(inst.rd()) = (full >> 32) as u32;
                            }
                        }
                        _ => todo!(), // raise reserved
                    },
                    Special::SOP32 => match inst.sa().value() {
                        // DIV
                        0b00010 => {
                            *self.gpr_mut(inst.rd()) = (self.gpr(inst.rs()) as i32)
                                .checked_div(self.gpr(inst.rt()) as i32)
                                .unwrap_or_else(|| {
                                    self.unpredictable = true;
                                    0
                                }) as u32;
                        }
                        // MOD
                        0b00011 => {
                            *self.gpr_mut(inst.rd()) = (self.gpr(inst.rs()) as i32)
                                .checked_rem(self.gpr(inst.rs()) as i32)
                                .unwrap_or_else(|| {
                                    self.unpredictable = true;
                                    0
                                }) as u32;
                        }
                        _ => todo!(), // raise reserved
                    },
                    Special::SOP33 => match inst.sa().value() {
                        // DIVU
                        0b00010 => {
                            *self.gpr_mut(inst.rd()) = self
                                .gpr(inst.rs())
                                .checked_div(self.gpr(inst.rt()))
                                .unwrap_or_else(|| {
                                    self.unpredictable = true;
                                    0
                                });
                        }
                        // MODU
                        0b00011 => {
                            *self.gpr_mut(inst.rd()) = self
                                .gpr(inst.rs())
                                .checked_rem(self.gpr(inst.rs()))
                                .unwrap_or_else(|| {
                                    self.unpredictable = true;
                                    0
                                });
                        }
                        _ => todo!(), // raise reserved
                    },
                    Special::ADD => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        self.gpr(inst.rs())
                            .checked_add(self.gpr(inst.rt()))
                            .map_or_else(
                                || {
                                    // as the spec states, $rd is not modified on overflow
                                    todo!(); // raise integer overflow
                                },
                                |sum| {
                                    *self.gpr_mut(inst.rd()) = sum;
                                },
                            );
                    }
                    Special::ADDU => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) =
                            self.gpr(inst.rs()).wrapping_add(self.gpr(inst.rd()));
                    }
                    Special::SUB => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        self.gpr(inst.rs())
                            .checked_sub(self.gpr(inst.rt()))
                            .map_or_else(
                                || {
                                    // same as ADD here; we don't touch $rd on overflow
                                    todo!(); // raise integer overflow
                                },
                                |sum| {
                                    *self.gpr_mut(inst.rd()) = sum;
                                },
                            );
                    }
                    Special::SUBU => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) =
                            self.gpr(inst.rs()).wrapping_sub(self.gpr(inst.rd()));
                    }
                    Special::AND => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = self.gpr(inst.rs()) & self.gpr(inst.rt());
                    }
                    Special::OR => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = self.gpr(inst.rs()) | self.gpr(inst.rt());
                    }
                    Special::XOR => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = self.gpr(inst.rs()) ^ self.gpr(inst.rt());
                    }
                    Special::NOR => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = !(self.gpr(inst.rs()) | self.gpr(inst.rt()));
                    }
                    Special::SLT => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) =
                            if (self.gpr(inst.rs()) as i32) < (self.gpr(inst.rt()) as i32) {
                                1
                            } else {
                                0
                            };
                    }
                    Special::SLTU => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = if self.gpr(inst.rs()) < self.gpr(inst.rt()) {
                            1
                        } else {
                            0
                        };
                    }
                    Special::TGE => {
                        if self.gpr(inst.rs()) as i32 >= self.gpr(inst.rt()) as i32 {
                            // signal_exception(Exception::Trap)
                            todo!();
                        }
                    }
                    Special::TGEU => {
                        if self.gpr(inst.rs()) >= self.gpr(inst.rt()) {
                            // signal_exception(Exception::Trap)
                            todo!();
                        }
                    }
                    Special::TLT => {
                        if (self.gpr(inst.rs()) as i32) < (self.gpr(inst.rt()) as i32) {
                            // signal_exception(Exception::Trap)
                            todo!();
                        }
                    }
                    Special::TLTU => {
                        if self.gpr(inst.rs()) < self.gpr(inst.rt()) {
                            // signal_exception(Exception::Trap)
                            todo!();
                        }
                    }
                    Special::TEQ => {
                        if self.gpr(inst.rs()) == self.gpr(inst.rt()) {
                            // signal_exception(Exception::Trap)
                            todo!();
                        }
                    }
                    Special::SELEQZ => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = if self.gpr(inst.rt()) == 0 {
                            self.gpr(inst.rs())
                        } else {
                            0
                        };
                    }
                    Special::TNE => {
                        if self.gpr(inst.rs()) != self.gpr(inst.rt()) {
                            // signal_exception(Exception::Trap)
                            todo!();
                        }
                    }
                    Special::SELNEZ => {
                        if inst.sa().value() != 0 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = if self.gpr(inst.rt()) != 0 {
                            self.gpr(inst.rs())
                        } else {
                            0
                        };
                    }
                };
            }
            Opcode::REGIMM => {
                use inst::regimm::Regimm;
                let inst = inst::Imm16Inst::new_with_raw_value(inst.raw_value());

                match match Regimm::new_with_raw_value(inst.rt()) {
                    Ok(rt) => rt,
                    Err(_) => return todo!(),
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
            Opcode::ADDIU => {
                let inst = inst::Imm16Inst::new_with_raw_value(inst.raw_value());

                *self.gpr_mut(inst.rt()) = self
                    .gpr(inst.rs())
                    .wrapping_add(inst.immediate() as i32 as u32);
            }
            Opcode::SLTI => todo!(),
            Opcode::SLTIU => todo!(),
            Opcode::ANDI => {
                let inst = inst::Imm16Inst::new_with_raw_value(inst.raw_value());

                *self.gpr_mut(inst.rt()) = self.gpr(inst.rs()) & (inst.immediate() as u32);
            }
            Opcode::ORI => {
                let inst = inst::Imm16Inst::new_with_raw_value(inst.raw_value());

                *self.gpr_mut(inst.rt()) = self.gpr(inst.rs()) | (inst.immediate() as u32);
            }
            Opcode::XORI => {
                let inst = inst::Imm16Inst::new_with_raw_value(inst.raw_value());

                *self.gpr_mut(inst.rt()) = self.gpr(inst.rs()) ^ (inst.immediate() as u32);
            }
            Opcode::AUI => todo!(), // TODO: LUI
            Opcode::COP0 => todo!(),
            Opcode::COP1 => todo!(),
            Opcode::COP2 => todo!(),
            Opcode::POP26 => todo!(), // TODO: BGEZC, BLEZC, BGEC
            Opcode::POP27 => todo!(), // TODO: BLTZC, BGTZC, BLTC
            Opcode::POP30 => todo!(), // TODO: BNEZALC, BNEC, BNVC
            Opcode::MSA => todo!(),
            Opcode::SPECIAL3 => {
                use inst::special3::{Special3, Special3Inst};

                match match Special3Inst::new_with_raw_value(inst.raw_value()).function() {
                    Ok(function) => function,
                    Err(_) => return todo!(),
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
