// TODO: uncommment this when https://github.com/rust-lang/rust/issues/48665
// gets fixed some day, or if there's a better workaround
// #![no_std]
#![deny(clippy::alloc_instead_of_core)]
#![deny(clippy::allow_attributes_without_reason)]
// TODO: enable this when clippy hits 1.66.0
// #![deny(clippy::as_ptr_cast_mut)]
#![deny(clippy::cast_possible_truncation)]
#![deny(clippy::dbg_macro)]
#![deny(clippy::equatable_if_let)]
#![deny(clippy::filter_map_next)]
#![deny(clippy::flat_map_option)]
#![deny(clippy::map_unwrap_or)]
#![deny(clippy::missing_panics_doc)]
#![deny(clippy::option_if_let_else)]
#![deny(clippy::panic)]
#![deny(clippy::std_instead_of_alloc)]
#![deny(clippy::std_instead_of_core)]
#![deny(clippy::todo)]
#![deny(clippy::wildcard_enum_match_arm)]
#![deny(clippy::wildcard_imports)]
#![deny(macro_use_extern_crate)]
// TODO: enable this when things are stable
// #![deny(missing_docs)]
#![deny(unused_crate_dependencies)]
#![deny(unused_extern_crates)]
#![deny(unused_lifetimes)]
#![deny(unused_qualifications)]

pub mod inst;
pub mod test;

use core::mem::size_of;
use core::mem::transmute;

// TODO: *_ptr::add is technically unsafe here, because it requires that index
// cannot overflow an isize, so if someone managed to allocate an array larger
// than half the accessible memory for an architecture, this could technically
// break

pub trait IndexAligned {
    /// # Safety
    ///
    /// This transmutes self[index..index + size_of::<T>()] into T, so all the usual warnings apply
    /// with transmuting.
    unsafe fn index_aligned<T: Copy>(&self, index: usize) -> T;
}

impl IndexAligned for &[u8] {
    unsafe fn index_aligned<T: Copy>(&self, index: usize) -> T {
        assert!(self.len() > index + (size_of::<T>() - 1));
        *(self.as_ptr().add(index) as *const T)
    }
}

impl IndexAligned for &mut [u8] {
    unsafe fn index_aligned<T: Copy>(&self, index: usize) -> T {
        assert!(self.len() > index + (size_of::<T>() - 1));
        *(self.as_ptr().add(index) as *const T)
    }
}

pub trait IndexAlignedMut {
    /// # Safety
    ///
    /// This transmutes self[index..index + size_of::<T>()] into T, so all the usual warnings apply
    /// with transmuting.
    unsafe fn index_aligned_mut<T>(&mut self, index: usize) -> &mut T;
}

impl IndexAlignedMut for &mut [u8] {
    unsafe fn index_aligned_mut<T>(&mut self, index: usize) -> &mut T {
        assert!(self.len() > index + (size_of::<T>() - 1));
        (self.as_mut_ptr().add(index) as *mut T).as_mut().unwrap()
    }
}

pub fn u32_from_ne_hwords(hwords: [u16; 2]) -> u32 {
    unsafe { transmute(hwords) }
}

pub trait UnreachableUnwrap<T> {
    fn unreachable_unwrap(self) -> T;
}

impl<T, U> UnreachableUnwrap<T> for Result<T, U> {
    fn unreachable_unwrap(self) -> T {
        match self {
            Ok(v) => v,
            Err(_) => unreachable!(),
        }
    }
}

impl<T> UnreachableUnwrap<T> for Option<T> {
    fn unreachable_unwrap(self) -> T {
        match self {
            Some(v) => v,
            None => unreachable!(),
        }
    }
}
