pub mod opcode;
pub mod regimm;
pub mod special;
pub mod special3;

pub type Inst = u32;
pub trait InstFields {
    fn opcode(&self) -> u8;
}
impl InstFields for Inst {
    #[inline(always)]
    fn opcode(&self) -> u8 {
        (self >> 26) as u8
    }
}
