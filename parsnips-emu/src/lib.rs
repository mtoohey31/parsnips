#![no_std]
#![deny(
    clippy::alloc_instead_of_core,
    clippy::allow_attributes_without_reason,
    // TODO: enable this when clippy hits 1.66.0
    // clippy::as_ptr_cast_mut,
    clippy::cast_possible_truncation,
    // TODO: uncomment after dbg!()'s are removed
    // clippy::dbg_macro,
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

use arbitrary_int::{u5, u6};
use parsnips_util::{reg::Reg, IndexAligned};
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

    fn gpr(&self, index: Reg) -> u32 {
        self.gprs[index.raw_value().value() as usize]
    }

    /// Retrieve a mutable reference to the general purose register index, unless index == 0, in
    /// which case this function returns a mutable reference to a value that will never be read.
    ///
    /// This is consistent with the definition of $zero in vol II-A table 1.2 of the spec, where it
    /// indicates that non-zero writes should be ignored.
    fn gpr_mut(&mut self, index: Reg) -> &mut u32 {
        let index = index.raw_value().value() as usize;
        if index == 0 {
            return unsafe { &mut GARBAGE };
        }
        &mut self.gprs[index]
    }

    // NOTE: step must take memory as parameter instead of it being provided it to Emulator::new
    // because wasm_bindgen values cannot have lifetimes
    // TODO: figure out how to fix this, even if it means dropping wasm_bindgen and making the js
    // bindings unsafe

    pub fn step(&mut self, memory: &mut [u32]) {
        use parsnips_util::inst::{self, Opcode};

        if (self.pc / 4) as usize >= memory.len() {
            todo!();
        }
        let inst = if self.pc % 4 == 0 {
            inst::Inst::new_with_raw_value(memory[self.pc as usize / 4])
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
                        if inst.rs() == Reg::Zero
                            && inst.rt() == Reg::Zero
                            && inst.rd() == Reg::Zero
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
                        match inst.rs().raw_value().value() {
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
                        if inst.rs() != Reg::Zero {
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
                                << ((inst.sa().value() & 0b11) + 1))
                                + self.gpr(inst.rt());
                            // TODO: could the added value cause this to overflow and panic?
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
                        if inst.rt() != Reg::Zero || inst.sa().value() != 1 {
                            self.unpredictable = true;
                        }

                        *self.gpr_mut(inst.rd()) = self.gpr(inst.rs()).leading_zeros();
                    }
                    Special::CLO => {
                        if inst.rt() != Reg::Zero || inst.sa().value() != 1 {
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
                            // same as above, but with the upper bits instead this time
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
                                .checked_rem(self.gpr(inst.rt()) as i32)
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
                            self.gpr(inst.rs()).wrapping_add(self.gpr(inst.rt()));
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
                            self.gpr(inst.rs()).wrapping_sub(self.gpr(inst.rt()));
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

                match match Regimm::new_with_raw_value(inst.rt().raw_value()) {
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
                    .wrapping_add(inst.immediate() as i16 as i32 as u32);
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

#[cfg(test)]
mod tests {
    use std::dbg;

    use super::*;
    extern crate alloc;
    extern crate std;
    use alloc::vec::Vec;
    use parsnips_util::inst::{special::Special, Imm16Inst, Inst, Opcode, RInst};

    fn run(starting_memory: &[u32]) -> (Emulator, Vec<u32>) {
        let mut memory = starting_memory.to_vec();
        let mut emu = Emulator::new();
        for _ in 0..memory.len() {
            emu.step(&mut memory);
        }
        (emu, memory)
    }

    #[test]
    fn sll() {
        let v = 2;
        let sa = 4;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rs(Reg::Zero)
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
            // sll $t1, $t0, sa
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_rd(Reg::T1)
            .with_sa(u5::new(sa))
            .with_function(Special::SLL)
            .raw_value(),
        ]);
        assert_eq!((v as u32) << sa, emu.gpr(Reg::T1));
    }

    #[test]
    fn srl() {
        let v = 200;
        let sa = 4;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
            // srl $t1, $t0, sa
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_rd(Reg::T1)
            .with_sa(u5::new(sa))
            .with_function(Special::SRL)
            .raw_value(),
        ]);
        assert_eq!((v as u32) >> sa, emu.gpr(Reg::T1));
    }

    #[test]
    fn rotr() {
        let v = 0b1010111001001;
        let sa = 4;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
            // rotr $t1, $t0, sa
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::new_with_raw_value(u5::new(1)))
            .with_rt(Reg::T0)
            .with_rd(Reg::T1)
            .with_sa(u5::new(sa))
            .with_function(Special::SRL)
            .raw_value(),
        ]);
        assert_eq!((v as u32).rotate_right(sa as u32), emu.gpr(Reg::T1));
    }

    #[test]
    fn sra() {
        let v = 200;
        let sa = 4;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
            // sra $t1, $t0, sa
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_rd(Reg::T1)
            .with_sa(u5::new(sa))
            .with_function(Special::SRA)
            .raw_value(),
        ]);
        assert_eq!(((v as i32) >> sa) as u32, emu.gpr(Reg::T1));
    }

    #[test]
    fn sllv() {
        let v = 2;
        let sa = 4;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
            // addiu $t1, $zero, sa
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(sa)
            .raw_value(),
            // sllv $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T1)
            .with_rt(Reg::T0)
            .with_rd(Reg::T2)
            .with_function(Special::SLLV)
            .raw_value(),
        ]);
        assert_eq!((v as u32) << sa, emu.gpr(Reg::T2));
    }

    #[test]
    fn lsa() {
        let v1 = 2;
        let v2 = 5;
        let sa = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // lsa $t2, $t0, $t1, sa
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(sa))
            .with_function(Special::LSA)
            .raw_value(),
        ]);
        assert_eq!(((v1 as u32) << (sa + 1)) + v2 as u32, emu.gpr(Reg::T2));
    }

    #[test]
    fn srlv() {
        let v = 200;
        let sa = 4;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
            // addiu $t1, $zero, sa
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(sa)
            .raw_value(),
            // srlv $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T1)
            .with_rt(Reg::T0)
            .with_rd(Reg::T2)
            .with_function(Special::SRLV)
            .raw_value(),
        ]);
        assert_eq!((v as u32) >> sa, emu.gpr(Reg::T2));
    }

    #[test]
    fn rotrv() {
        let v = 0b1010111001001;
        let sa = 4;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
            // addiu $t1, $zero, sa
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(sa)
            .raw_value(),
            // rotrv $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T1)
            .with_rt(Reg::T0)
            .with_rd(Reg::T2)
            .with_sa(u5::new(1))
            .with_function(Special::SRLV)
            .raw_value(),
        ]);
        assert_eq!((v as u32).rotate_right(sa as u32), emu.gpr(Reg::T2));
    }

    #[test]
    fn srav() {
        let v: i16 = -200;
        let sa = 4;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v as u16)
            .raw_value(),
            // addiu $t1, $zero, sa
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(sa)
            .raw_value(),
            // srav $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T1)
            .with_rt(Reg::T0)
            .with_rd(Reg::T2)
            .with_function(Special::SRAV)
            .raw_value(),
        ]);
        assert_eq!(((v as i32) >> sa) as u32, emu.gpr(Reg::T2));
    }

    #[test]
    fn clz() {
        let v = i16::MAX as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
            // clz $t1, $t0
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rd(Reg::T1)
            .with_function(Special::CLZ)
            .raw_value(),
        ]);
        assert_eq!((v as u32).leading_zeros(), emu.gpr(Reg::T1));
    }

    #[test]
    fn clo() {
        let v = -1_i16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v as u16)
            .raw_value(),
            // clo $t1, $t0
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rd(Reg::T1)
            .with_function(Special::CLO)
            .raw_value(),
        ]);
        assert_eq!((v as i32).leading_ones(), emu.gpr(Reg::T1));
    }

    #[test]
    fn mul() {
        let v1 = 3;
        let v2 = -7_i16 as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // mul $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(0b10))
            .with_function(Special::SOP30)
            .raw_value(),
        ]);
        assert_eq!(
            ((v1 as i16 as i32) * (v2 as i16 as i32)) as u32,
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn muh() {
        let v1 = 3;
        let v2 = -7_i16 as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // muh $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(0b11))
            .with_function(Special::SOP30)
            .raw_value(),
        ]);
        assert_eq!(
            (((v1 as i16 as i64) * (v2 as i16 as i64)) >> 32) as u32,
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn mulu() {
        let v1 = 3;
        let v2 = -7_i16 as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // mulu $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(0b10))
            .with_function(Special::SOP31)
            .raw_value(),
        ]);
        assert_eq!(
            (((v1 as u64) * (v2 as i16 as i32 as u32 as u64)) & ((1 << 32) - 1)) as u32,
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn muhu() {
        let v1 = 3;
        let v2 = -7_i16 as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // muhu $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(0b11))
            .with_function(Special::SOP31)
            .raw_value(),
        ]);
        assert_eq!(
            (((v1 as u64) * (v2 as i16 as i32 as u32 as u64)) >> 32) as u32,
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn div() {
        let v1 = -7_i16 as u16;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // div $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(0b10))
            .with_function(Special::SOP32)
            .raw_value(),
        ]);
        assert_eq!(
            ((v1 as i16 as i32) / (v2 as i16 as i32)) as u32,
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn r#mod() {
        let v1 = -7_i16 as u16;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // mod $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(0b11))
            .with_function(Special::SOP32)
            .raw_value(),
        ]);
        assert_eq!(
            ((v1 as i16 as i32) % (v2 as i16 as i32)) as u32,
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn divu() {
        let v1 = -7_i16 as u16;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // divu $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(0b10))
            .with_function(Special::SOP33)
            .raw_value(),
        ]);
        assert_eq!((v1 as i16 as i32 as u32) / v2 as u32, emu.gpr(Reg::T2));
    }

    #[test]
    fn modu() {
        let v1 = -7_i16 as u16;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // modu $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_sa(u5::new(0b11))
            .with_function(Special::SOP33)
            .raw_value(),
        ]);
        assert_eq!((v1 as i16 as i32 as u32) % (v2 as u32), emu.gpr(Reg::T2));
    }

    #[test]
    fn add() {
        let v1 = -7_i16 as u16;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // add $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::ADD)
            .raw_value(),
        ]);
        assert_eq!(
            ((v1 as i16 as i32) + (v2 as i16 as i32)) as u32,
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn addu() {
        let v1 = -7_i16 as u16;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // addu $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::ADDU)
            .raw_value(),
        ]);
        assert_eq!((v1 as i16 as i32 as u32) + (v2 as u32), emu.gpr(Reg::T2));
    }

    #[test]
    fn sub() {
        let v1 = -7_i16 as u16;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // sub $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SUB)
            .raw_value(),
        ]);
        assert_eq!(
            ((v1 as i16 as i32) - (v2 as i16 as i32)) as u32,
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn subu() {
        let v1 = -7_i16 as u16;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // subu $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SUBU)
            .raw_value(),
        ]);
        assert_eq!((v1 as i16 as i32 as u32) - (v2 as u32), emu.gpr(Reg::T2));
    }

    #[test]
    fn and() {
        let v1 = 0b10110101101011;
        let v2 = 0b01101101110111;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // and $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::AND)
            .raw_value(),
        ]);
        assert_eq!((v1 as u32) & (v2 as u32), emu.gpr(Reg::T2));
    }

    #[test]
    fn or() {
        let v1 = 0b10110101101011;
        let v2 = 0b01101101110111;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // or $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::OR)
            .raw_value(),
        ]);
        assert_eq!((v1 as u32) | (v2 as u32), emu.gpr(Reg::T2));
    }

    #[test]
    fn xor() {
        let v1 = 0b10110101101011;
        let v2 = 0b01101101110111;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // xor $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::XOR)
            .raw_value(),
        ]);
        assert_eq!((v1 as u32) ^ (v2 as u32), emu.gpr(Reg::T2));
    }

    #[test]
    fn nor() {
        let v1 = 0b10110101101011;
        let v2 = 0b01101101110111;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // nor $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::NOR)
            .raw_value(),
        ]);
        assert_eq!(!((v1 as u32) | (v2 as u32)), emu.gpr(Reg::T2));
    }

    #[test]
    fn slt() {
        let v1 = 1;
        let v2 = -1_i16 as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // slt $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SLT)
            .raw_value(),
        ]);
        assert_eq!(
            if (v1 as i16) < (v2 as i16) { 1 } else { 0 },
            emu.gpr(Reg::T2)
        );

        let v1 = -37_i16 as u16;
        let v2 = -1_i16 as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // slt $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SLT)
            .raw_value(),
        ]);
        assert_eq!(
            if (v1 as i16) < (v2 as i16) { 1 } else { 0 },
            emu.gpr(Reg::T2)
        );
    }

    #[test]
    fn sltu() {
        let v1 = 9;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // sltu $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SLTU)
            .raw_value(),
        ]);
        assert_eq!(if v1 < v2 { 1 } else { 0 }, emu.gpr(Reg::T2));

        let v1 = -37_i16 as u16;
        let v2 = -1_i16 as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // sltu $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SLTU)
            .raw_value(),
        ]);
        assert_eq!(if v1 < v2 { 1 } else { 0 }, emu.gpr(Reg::T2));
    }

    #[test]
    fn seleqz() {
        let v1 = 9;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // seleqz $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SELEQZ)
            .raw_value(),
        ]);
        assert_eq!(if v2 == 0 { v1 as u32 } else { 0 }, emu.gpr(Reg::T2));

        let v1 = 9;
        let v2 = 0;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // seleqz $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SELEQZ)
            .raw_value(),
        ]);
        assert_eq!(if v2 == 0 { v1 as u32 } else { 0 }, emu.gpr(Reg::T2));
    }

    #[test]
    fn selnez() {
        let v1 = 9;
        let v2 = 3;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // seleqz $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SELNEZ)
            .raw_value(),
        ]);
        assert_eq!(if v2 != 0 { v1 as u32 } else { 0 }, emu.gpr(Reg::T2));

        let v1 = 9;
        let v2 = 0;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // addiu $t1, $zero, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
            // seleqz $t2, $t0, $t1
            RInst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::SPECIAL)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_rd(Reg::T2)
            .with_function(Special::SELNEZ)
            .raw_value(),
        ]);
        assert_eq!(if v2 != 0 { v1 as u32 } else { 0 }, emu.gpr(Reg::T2));
    }

    #[test]
    fn addiu() {
        let v = 9;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
        ]);
        assert_eq!(v as u32, emu.gpr(Reg::T0));

        let v = -9_i16 as u16;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v)
            .raw_value(),
        ]);
        assert_eq!(v as i16 as i32 as u32, emu.gpr(Reg::T0));
    }

    #[test]
    fn andi() {
        let v1 = 0b11011010110101;
        let v2 = 0b10101100111011;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // andi $t1, $t0, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ANDI)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
        ]);
        assert_eq!((v1 & v2) as u32, emu.gpr(Reg::T1));
    }

    #[test]
    fn ori() {
        let v1 = 0b11011010110101;
        let v2 = 0b10101100111011;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // ori $t1, $t0, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ORI)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
        ]);
        assert_eq!((v1 | v2) as u32, emu.gpr(Reg::T1));
    }

    #[test]
    fn xori() {
        let v1 = 0b11011010110101;
        let v2 = 0b10101100111011;
        let (emu, _) = run(&[
            // addiu $t0, $zero, v1
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::ADDIU)
                    .raw_value(),
            )
            .with_rt(Reg::T0)
            .with_immediate(v1)
            .raw_value(),
            // xori $t1, $t0, v2
            Imm16Inst::new_with_raw_value(
                Inst::new_with_raw_value(0)
                    .with_opcode(Opcode::XORI)
                    .raw_value(),
            )
            .with_rs(Reg::T0)
            .with_rt(Reg::T1)
            .with_immediate(v2)
            .raw_value(),
        ]);
        assert_eq!((v1 ^ v2) as u32, emu.gpr(Reg::T1));
    }
}
