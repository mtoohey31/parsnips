#[macro_export]
macro_rules! count {
    () => (0usize);
    ( $x:tt $($xs:tt)* ) => (1usize + count!($($xs)*));
}

#[macro_export]
macro_rules! ne_byte_arr {
    ($($w:expr),+ $(,)?) => {
        {
            use parsnips_util::count;
            let count = parsnips_util::count!($($w)*);
            unsafe{ core::mem::transmute::<[u32; count], [u8; count*4]>([$($w),+]) }
        }
    }
}
