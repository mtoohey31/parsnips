// TODO: uncommment this when https://github.com/rust-lang/rust/issues/48665
// gets fixed some day, or if there's a better workaround
// #![no_std]

pub mod inst;
use core::mem::size_of;

pub use inst::{Funct, Inst, Op};

// TODO: *_ptr::add is technically unsafe here, because it requires that index
// cannot overflow an isize, so if someone managed to allocate an array larger
// than half the accessible memory for an architecture, this could technically
// break

pub trait IndexAligned {
    fn index_aligned<T: Copy>(&self, index: usize) -> T;
}

impl IndexAligned for &[u8] {
    fn index_aligned<T: Copy>(&self, index: usize) -> T {
        assert!(self.len() > index + (size_of::<T>() - 1));
        unsafe { *(self.as_ptr().add(index) as *const T) }
    }
}

impl IndexAligned for &mut [u8] {
    fn index_aligned<T: Copy>(&self, index: usize) -> T {
        assert!(self.len() > index + (size_of::<T>() - 1));
        unsafe { *(self.as_ptr().add(index) as *const T) }
    }
}

pub trait IndexAlignedMut {
    fn index_aligned_mut<T>(&mut self, index: usize) -> &mut T;
}

impl IndexAlignedMut for &mut [u8] {
    fn index_aligned_mut<T>(&mut self, index: usize) -> &mut T {
        assert!(self.len() > index + (size_of::<T>() - 1));
        unsafe { (self.as_mut_ptr().add(index) as *mut T).as_mut().unwrap() }
    }
}
