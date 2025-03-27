//! Treerder, retrieval tree orderer, orders any `Orderable` implementing type by its `char`s sequence representation . Oob support for `&str` and `String` and English alphabet A–Za–z.

use std::vec::Vec;
use core::mem::{forget, replace};

/// `impl Orderable` is type which is ordable by its
/// `char` sequence representation.
///
/// Careful implementation needed. When wrongly implemented,
/// various errors can occur including process aborting.
/// See `Shadow` associated type for more information.
///
/// Craft behing this is that `Orderable` trait allows for perfomance
/// optimization by avoiding excessive scenarios like deep cloning and others.
///
/// Check this phantasmal implementation for `usize`.
/// `Orderable` implementation cannot work without providing `Treerder` with
/// appropriate alphabet same as function for `char` index generation.
/// ```
/// use treerder::{Orderable, Treerder};
///
/// #[derive(Debug, PartialEq)]
/// struct LocalUsize(usize);
///
/// struct LocalUsizeCharIterator {
///     s: String,
///     c: usize,
/// }
///
/// impl Iterator for LocalUsizeCharIterator {
///     type Item = char;
///
///     fn next(&mut self) -> Option<char> {
///         let c = self.c;
///
///         let opt = self.s.chars().nth(c);
///
///         if opt.is_some() {
///             self.c = c + 1;
///         }
///
///         opt
///     }
/// }
///
/// impl Orderable for LocalUsize {
///     type Shadow = usize;
///
///     fn chars(&self) -> impl Iterator<Item = char> {
///         LocalUsizeCharIterator {
///             s: self.0.to_string(),
///             c: 0,
///         }
///     }
///
///     fn shadow(&self) -> Self::Shadow {
///         self.0
///     }
///
///     fn steady(s: Self::Shadow) -> Self {
///         LocalUsize(s)
///     }
/// }
///
/// fn ix(c: char) -> usize {
///     c.to_digit(10).unwrap() as usize
/// }
///
/// let mut nums = [999, 333, 33, 3, 0, 100, 10, 1].map(|x| LocalUsize(x));
///
/// let mut orderer = Treerder::new_with(ix, 10);
/// orderer.order(&mut nums);
///
/// let proof = [0, 1, 10, 100, 3, 33, 333, 999].map(|x| LocalUsize(x));
/// assert_eq!(proof, nums);
///
/// ```
pub trait Orderable {
    /// Type that will represent `impl Orderable` in internal structures.
    ///
    /// For heap allocated types providing raw pointer is sufficient while
    /// for stack allocations full reproduction is needed.
    ///
    /// Check implementations for `&str` and `String`
    /// for understandable examples.
    type Shadow;

    /// Returns `Iterator<Item = char>` implementation used for ordering.
    fn chars(&self) -> impl Iterator<Item = char>;
    /// Provides backing type to be stored in internal structure.
    fn shadow(&self) -> Self::Shadow;
    /// Converts backing back to Self.
    fn steady(s: Self::Shadow) -> Self;
}

impl<'a> Orderable for &'a str {
    type Shadow = &'a str;

    fn chars(&self) -> impl Iterator<Item = char> {
        (*self).chars()
    }

    /// It is simple to pass `&str` around as its cloning is cheap.
    fn shadow(&self) -> Self::Shadow {
        *self
    }

    fn steady(s: Self::Shadow) -> Self {
        s
    }
}

impl Orderable for String {
    type Shadow = String;

    fn chars(&self) -> impl Iterator<Item = char> {
        (&**self).chars()
    }

    /// Cloning `String` is deep copy operation. `shadow` avoids this.
    fn shadow(&self) -> Self::Shadow {
        let ptr = self as *const String;
        unsafe { ptr.read() }
    }

    fn steady(s: Self::Shadow) -> Self {
        s
    }
}

/// `Letter` is `Alphabet` element, represents tree node.
#[cfg_attr(test, derive(PartialEq))]
struct Letter<T>
where
    T: Orderable,
{
    #[cfg(test)]
    val: char,
    ab: Option<Alphabet<T>>,
    ens: Option<Entries<T::Shadow>>,
}

impl<T> Letter<T>
where
    T: Orderable,
{
    const fn new() -> Self {
        Letter {
            #[cfg(test)]
            val: '🫀',
            ab: None,
            ens: None,
        }
    }
}

/// Tree node arms. Consists of `Letter`s.
type Alphabet<T> = Box<[Letter<T>]>;
/// Index conversion function. Tighten with alphabet used.
/// Returns corresponding `usize`d index of `char`.
///
/// For details see `english_letters::ix` implementation.
pub type Ix = fn(char) -> usize;

type Entries<T> = Vec<T>;

/// Alphabet function, tree arms generation of length specified.
fn ab<T>(len: usize) -> Alphabet<T>
where
    T: Orderable,
{
    let mut ab = Vec::new();
    ab.reserve_exact(len);

    #[cfg(test)]
    #[cfg(feature = "test-ext")]
    let mut c = 'A' as u8;

    let sc = ab.spare_capacity_mut();
    for ix in 0..len {
        let mut _letter = sc[ix].write(Letter::new());

        #[cfg(test)]
        #[cfg(feature = "test-ext")]
        {
            _letter.val = c as char;

            const Z: u8 = 'Z' as u8;
            c = if c == Z { 'a' as u8 } else { c + 1 }
        }
    }

    unsafe { ab.set_len(len) };

    ab.into_boxed_slice()
}

/// Module for working with English alphabet letters, A-Za-z.
///
/// For details see `Treerder::new_with()`.
pub mod english_letters {

    /// 26
    pub const BASE_ALPHABET_LEN: usize = 26;
    /// 52
    pub const ALPHABET_LEN: usize = BASE_ALPHABET_LEN * 2;

    /// Index conversion function.
    pub fn ix(c: char) -> usize {
        let code_point = c as usize;

        const A: usize = 'A' as usize;
        #[allow(non_upper_case_globals)]
        const a: usize = 'a' as usize;

        match code_point {
            | c if c > 64 && c < 91 => c - A,
            | c if c > 96 && c < 123 => c - a + BASE_ALPHABET_LEN,
            | _ => {
                panic!("Index conversion failed because code point {code_point} is unsupported.")
            },
        }
    }
}

// TC: Θ(n ⋅ alphabet size + e) ⇒ Θ(n), n = nodes count, e = entries count
fn exc<'b, T>(ab: &'b mut Alphabet<T>, ts: &mut [T], mut wr_ix: usize) -> usize
where
    T: Orderable,
{
    for ix in 0..ab.len() {
        let letter = &mut ab[ix];
        if let Some(ens) = letter.ens.as_mut() {
            let ens_ptr = ens.as_ptr();
            for ix in 0..ens.len() {
                let e = unsafe {
                    let ptr = ens_ptr.add(ix);
                    ptr.read()
                };

                let steady = Orderable::steady(e);
                let some = replace(&mut ts[wr_ix], steady);

                // `Orderable` implementation should bond reconstructed type
                // obligation to be fully-fledged replacement
                // omitting `drop` for any moved-out value is then desirable
                forget(some);

                wr_ix += 1;
            }

            unsafe {
                ens.set_len(0);
            }
        }

        if let Some(ab) = letter.ab.as_mut() {
            wr_ix = exc(ab, ts, wr_ix);
        }
    }

    wr_ix
}

/// `Treerder` is coupled with `Orderable`. Enables ordering of any `impl Orderable` type by
/// its `char` sequence representation.
///
/// For details see `fn order`.
pub struct Treerder {
    ix: Ix,
    al: usize,
}

impl Treerder {
    /// Constructs default version of `Treerder`, i.e. via
    /// `fn new_with()` with `english_letters::ALPHABET_LEN` and `english_letters::ix`.
    pub fn new() -> Self {
        Self::new_with(english_letters::ix, english_letters::ALPHABET_LEN)
    }

    /// Allows to use custom alphabet different from default alphabet. See `fn new()`.
    ///
    /// For details see module `english_letters`.
    pub fn new_with(ix: Ix, ab_len: usize) -> Self {
        Self { ix, al: ab_len }
    }

    /// Stable ordering.
    ///
    /// ⚠️ `impl Orderable` recreations made out of `Orderable::Shadow` replace
    /// _originals_ in input without dropping them.
    ///
    /// For details see `Orderable`.
    ///
    /// - TC: Ο(s) where s is sum of all `char`s iterated over.
    /// - SC: Θ(q) where q is number of unique nodes, i.e. `char`s in respective branches.
    pub fn order<T>(&mut self, ts: &mut [T])
    where
        T: Orderable,
    {
        let mut wr_ix = 0;

        let mut root = ab(self.al);
        for ix in 0..ts.len() {
            let curr = &ts[ix];
            let mut chars = curr.chars();

            if let Some(c) = chars.next() {
                let shad = curr.shadow();
                self.ins(&mut root, shad, c, &mut chars);
            } else {
                drop(chars);
                ts.swap(wr_ix, ix);
                wr_ix += 1;
            }
        }

        exc(&mut root, ts, wr_ix);
    }

    // TC: Θ(l), l = `cs` length
    // SC: Θ(q ⋅ alphabet size) ⇒ Θ(q) as long as q > alphabet size, q = unique nodes count, [leaf node does not have arms (alphabet)]
    fn ins<T>(
        &self,
        mut alphabet: &mut Alphabet<T>,
        entry: T::Shadow,
        mut c: char,
        cs: &mut impl Iterator<Item = char>,
    ) where
        T: Orderable,
    {
        let ix = self.ix;
        let al = self.al;

        loop {
            let c_ix = ix(c);
            let letter = &mut alphabet[c_ix];

            if let Some(cx) = cs.next() {
                c = cx;
                alphabet = letter.ab.get_or_insert_with(|| ab(al))
            } else {
                let ens = letter.ens.get_or_insert_with(|| Entries::new());
                ens.push(entry);
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests_of_units {

    use crate::{Letter, Orderable};
    use std::fmt::{Debug, Formatter};

    impl<T> Debug for Letter<T>
    where
        T: Orderable,
    {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let ab = some_none(self.ab.as_ref());
            let ens = some_none(self.ens.as_ref());

            return f.write_fmt(format_args!(
                "Letter {{\n  val: {:?}\n  ab: {}\n  ens: {}\n}}",
                self.val, ab, ens
            ));

            fn some_none<T>(val: Option<T>) -> &'static str {
                if val.is_some() {
                    "Some"
                } else {
                    "None"
                }
            }
        }
    }

    mod letter {

        use crate::Letter;

        #[test]
        fn new() {
            let letter = Letter::<&str>::new();

            assert_eq!('🫀', letter.val);
            assert!(letter.ab.is_none());
            assert!(letter.ens.is_none());
        }
    }

    mod ab {

        use crate::english_letters::ALPHABET_LEN;
        use crate::ab as ab_fn;

        #[test]
        fn ab() {
            let ab = ab_fn::<&str>(ALPHABET_LEN);
            assert_eq!(ALPHABET_LEN, ab.len());

            #[cfg(feature = "test-ext")]
            {
                let chain = ('A'..='Z').chain('a'..='z');

                for (ix, c) in chain.enumerate() {
                    let letter = &ab[ix];

                    assert_eq!(c, letter.val);
                    assert!(letter.ab.is_none());
                    assert!(letter.ens.is_none());
                }
            }
        }

        #[test]
        fn zero_len() {
            let ab = ab_fn::<&str>(0);
            assert_eq!(0, ab.len());
        }
    }

    mod english_letters {

        mod ix {
            use crate::english_letters::ix;
            use std::panic::catch_unwind;

            #[test]
            fn ixes() {
                assert_eq!(0, ix('A'));
                assert_eq!(25, ix('Z'));
                assert_eq!(26, ix('a'));
                assert_eq!(51, ix('z'));
            }

            #[test]
            fn unsupported_char() {
                let ucs = unsupported_chars();

                for (c, cp) in ucs.map(|x| (x as char, x)) {
                    let result = catch_unwind(|| ix(c));
                    assert!(result.is_err());

                    let err = result.err().unwrap();
                    let downcast = err.downcast_ref::<String>().unwrap();
                    let proof =
                        format!("Index conversion failed because code point {cp} is unsupported.");
                    assert_eq!(&proof, downcast);
                }
            }

            fn unsupported_chars() -> [u8; 4] {
                #[rustfmt::skip] let ucs =
                [
                    'A' as u8 -1, 'Z' as u8 +1, // 65–90
                    'a' as u8 -1, 'z' as u8 +1, // 97–122
                ];

                ucs
            }
        }
    }

    mod exc {
        use crate::{ab as ab_ctor, exc, Alphabet, Letter, Orderable};
        use crate::english_letters::{ALPHABET_LEN, ix};

        fn ab_fn<T: Orderable>() -> Alphabet<T> {
            ab_ctor(ALPHABET_LEN)
        }

        #[test]
        fn basic_test() {
            let mut ab = ab_fn();

            #[allow(non_snake_case)]
            let A = ["A1", "A2", "A3"];
            let z = ["z1", "z2", "z3"];

            ab[ix('A')].ens = Some(A.to_vec());
            ab[ix('z')].ens = Some(z.to_vec());

            let mut strs = [""; 7];

            exc(&mut ab, &mut strs, 1);

            assert_eq!("", strs[0]);

            let mut offset = 0;
            for s in A.iter().chain(z.iter()) {
                offset += 1;
                assert_eq!(*s, strs[offset]);
            }
        }

        #[test]
        fn nesting() {
            let mut root = ab_fn();
            let root = &mut root;

            #[rustfmt::skip]
            let ordered = [
                "A1", "A2", "A3", "z4", "z5", "z6",
                "B1", "B2", "B3", "y4", "y5", "y6",
                "y1", "y2", "y3", "B4", "B5", "B6",
                "z1", "z2", "z3", "A4", "A5", "A6",                
            ];

            prep(root, &ordered[0..3], &ordered[3..6]);
            prep(root, &ordered[6..9], &ordered[9..12]);
            prep(root, &ordered[12..15], &ordered[15..18]);
            prep(root, &ordered[18..21], &ordered[21..24]);

            let mut strs = [""; 24];

            exc(root, &mut strs, 0);

            let mut re_ix = 0;
            for s in ordered.iter() {
                assert_eq!(*s, strs[re_ix]);
                re_ix += 1;
            }

            fn prep<'a, 'b>(
                ab: &'b mut Alphabet<&'a str>,
                ent: &'b [&'a str],
                sub_ent: &'b [&'a str],
            ) {
                let c = ent[0].chars().next().unwrap();
                let sub_c = sub_ent[0].chars().next().unwrap();

                let l = &mut ab[ix(c)];

                let mut l_alphabet = ab_fn();
                let sub_l = &mut l_alphabet[ix(sub_c)];

                sub_l.ens = Some(sub_ent.to_vec());

                l.ab = Some(l_alphabet);
                l.ens = Some(ent.to_vec());
            }
        }

        #[test]
        #[allow(non_snake_case)]
        fn in_depth_recursion() {
            let mut root = ab_fn();
            let root = &mut root;

            // depth level described by numeric suffix
            // level: 10^(level-1) <= suffix < 10^level
            // ones for level 1, tens level 2, …
            #[rustfmt::skip]
            let ordered = [
                "A1", "A2", "A3", "A10", "A11", "A12", "z10", "z11", "z12", "B100", "B101", "B102", "q1000", "q1001", "q1002",
                "B1", "B2", "B3", "y10", "y11", "y12",
                "y1", "y2", "y3", "B10", "B11", "B12", "C100", "C101", "C102", "X100", "X101", "X102", "r1000", "r1001", "r1002",
            ];

            let A = add_ents_via_ab(root, &ordered[0..3]);
            _ = add_ents_via_le(A, &ordered[3..6]);
            let Az = add_ents_via_le(A, &ordered[6..9]);
            let AzB = add_ents_via_le(Az, &ordered[9..12]);
            _ = add_ents_via_le(AzB, &ordered[12..15]);

            let B = add_ents_via_ab(root, &ordered[15..18]);
            _ = add_ents_via_le(B, &ordered[18..21]);

            let y = add_ents_via_ab(root, &ordered[21..24]);
            let yB = add_ents_via_le(y, &ordered[24..27]);
            _ = add_ents_via_le(yB, &ordered[27..30]);
            let yBX = add_ents_via_le(yB, &ordered[30..33]);
            _ = add_ents_via_le(yBX, &ordered[33..36]);

            let mut strs = [""; 36];

            exc(root, &mut strs, 0);

            let mut re_ix = 0;
            for s in ordered.iter() {
                assert_eq!(*s, strs[re_ix]);
                re_ix += 1;
            }

            fn add_ents_via_le<'a, 'b>(
                le: &'b mut Letter<&'a str>,
                ent: &[&'a str],
            ) -> &'b mut Letter<&'a str> {
                let ab = le.ab.get_or_insert_with(|| ab_fn());
                add_ents_via_ab(ab, ent)
            }

            fn add_ents_via_ab<'a, 'b>(
                ab: &'b mut Alphabet<&'a str>,
                ent: &[&'a str],
            ) -> &'b mut Letter<&'a str> {
                let c = ent[0].chars().next().unwrap();
                let l = &mut ab[ix(c)];

                l.ens = Some(ent.to_vec());
                l
            }
        }

        /// `exc` must prevent double/early drop on values read from entries under letter
        /// also must prevent drop on values from original storage
        #[test]
        fn no_double_drop() {
            use core::cell::Cell;
            use std::rc::Rc;

            #[derive(Clone, PartialEq, Debug)]
            struct Dropper {
                s: String,
                c: Rc<Cell<usize>>,
            }

            impl Orderable for Dropper {
                type Shadow = Self;

                fn chars(&self) -> impl Iterator<Item = char> {
                    self.s.chars()
                }

                fn shadow(&self) -> Self {
                    unimplemented!("Not used in test.")
                }

                fn steady(s: Self::Shadow) -> Self {
                    s
                }
            }

            impl Drop for Dropper {
                fn drop(&mut self) {
                    if self.s == "" {
                        panic!("This should have never been executed.");
                    }

                    let c = self.c.get();
                    _ = self.c.replace(c + 1);
                }
            }

            let counter = Rc::new(Cell::new(0));

            #[allow(non_snake_case)]
            let A = Dropper {
                s: String::from("A"),
                c: counter.clone(),
            };

            let z = Dropper {
                s: String::from("z"),
                c: counter.clone(),
            };

            let mut ab = ab_fn();

            ab[ix('A')].ens = Some(vec![A.clone()]);
            ab[ix('z')].ens = Some(vec![z.clone()]);

            let filler = Dropper {
                s: String::from(""),
                c: counter.clone(),
            };

            let mut droppers = [filler.clone(), filler];

            exc(&mut ab, &mut droppers, 0);
            assert_eq!(0, counter.get());
            assert_eq!([A, z], droppers);
        }
    }

    mod treerder {
        use crate::Treerder;
        use crate::english_letters::{ix, ALPHABET_LEN};

        #[test]
        fn new() {
            let orderer = Treerder::new();
            assert_eq!(ALPHABET_LEN, orderer.al);
            assert_eq!(ix as usize, orderer.ix as usize);
        }

        #[test]
        fn new_with() {
            fn test_ix(_c: char) -> usize {
                0
            }

            let ab_len = 99;
            let orderer = Treerder::new_with(test_ix, ab_len);

            assert_eq!(ab_len, orderer.al);
            assert_eq!(test_ix as usize, orderer.ix as usize);
        }

        mod order {
            use crate::Treerder;

            #[test]
            #[allow(non_snake_case)]
            fn basic_test() {
                let ABC = "ABC";
                let ABD = "ABD";
                let ABE = "ABE";

                let zyu = "zyu";
                let zyv = "zyv";
                let zyx = "zyx";

                let mut strs = [zyx, zyu, zyv, ABC, ABE, ABD];

                let mut orderer = Treerder::new();
                orderer.order(&mut strs);

                #[rustfmt::skip]
                let proof = [
                    ABC, ABD, ABE,
                    zyu, zyv, zyx
                ];

                assert_eq!(proof, strs);

                let BC = "BC";
                let yx = "yx";

                let mut strs = [yx, BC];
                orderer.order(&mut strs);

                assert_eq!([BC, yx], strs);
            }

            #[test]
            fn stability() {
                let a1 = String::from("a");
                let a2 = String::from("a");
                let a3 = String::from("a");

                let b1 = String::from("b");
                let b2 = String::from("b");
                let b3 = String::from("b");

                assert_ne!(a1.as_ptr(), a2.as_ptr());

                // strict stability test not possible since all "" point to 0x1
                let emt1 = String::from("");
                let emt2 = String::from("");
                let emt3 = String::new();
                let emt4 = String::new();

                let (a1, a2, a3) = (&*a1, &*a2, &*a3);
                let (b1, b2, b3) = (&*b1, &*b2, &*b3);
                let (emt1, emt2, emt3, emt4) = (&*emt1, &*emt2, &*emt3, &*emt4);

                let mut strs = [emt1, b1, a1, emt2, b2, a2, emt3, b3, a3, emt4];

                let mut orderer = Treerder::new();
                orderer.order(&mut strs);

                #[rustfmt::skip]
                let proof = [
                    emt1, emt2, emt3, emt4,
                    a1, a2, a3,
                    b1, b2, b3,                   
                ];

                for ix in 0..strs.len() {
                    assert_eq!(proof[ix].as_ptr() as usize, strs[ix].as_ptr() as usize);
                }
            }

            #[test]
            #[allow(non_snake_case)]
            #[rustfmt::skip]
            fn load() {
                
                let ABC = "ABC"; let ABD = "ABD";                  
                let INSTANT = "INSTANT"; let JUNCTURE = "JUNCTURE"; let MOMENT = "MOMENT"; 
                
                let JUI = "JUI"; let JUN = "JUN"; 
                let XYA = "XYA"; let XYQ = "XYQ"; let XYZ = "XYZ"; 
                
                let XYAB = "XYAB";                
                let XYABA = "XYABA"; let XYABC = "XYABC";
                                
                let abc = "abc"; let abd = "abd";                
                let abcd = "abcd"; let abce = "abce";
                
                let qaa = "qaa"; 
                let qrs = "qrs"; let qrt = "qrt";                
                let qua = "qua"; let qwa = "qwa"; 
                
                let xya = "xya"; let xyz = "xyz"; 
                let zzaa = "zzaa"; let zzbb = "zzbb";                
                
                let percent = "percent"; let percentile = "percentile";
                
                let quail = "quail";
                let qualification = "qualification";
                let quality = "quality";
                let quantity = "quantity";
                
                let emt1 = ""; let emt2 = ""; let emt3 = "";
                
                let mut strs = [
                    XYZ, XYA, XYQ,
                    xyz, xya,
                    emt1,
                    zzbb, zzaa,
                    emt2,
                    ABC, ABD,
                    abce, abcd,
                    emt3,
                    abd, abc,
                    qwa, qua, qaa,
                    XYABC, XYABA, XYAB,
                    qrt, qrs,
                    percentile, percent,
                    quantity, quality, qualification, quail,
                    JUNCTURE, MOMENT, INSTANT,
                    JUI, JUN
                ];
                
                let mut proof = strs.clone();
                proof.sort();
                
                let mut orderer = Treerder::new();
                orderer.order(&mut strs);
                
                assert_eq!(proof, strs);
            }

            /// - `impl Orderable for String` uses as `Shadow` original instance duplication
            /// - `fn exc` uses `forget` to discard original instances while it
            /// trust in conversion from `Shadow` to _steady_ version of original
            /// - `fn order` uses `drop` so `chars` are surely _destructed_ and
            /// compiler satisfied
            #[test]
            fn no_mem_troubles() {
                let test: &mut [String] = &mut [
                    String::from("zzz"),
                    String::from(""),
                    String::from("ZZZ"),
                    String::from(""),
                    String::from("qqq"),
                    String::from(""),
                    String::from("QQQ"),
                    String::from(""),
                    String::from("lll"),
                    String::from(""),
                    String::from("LLL"),
                    String::from(""),
                    String::from("hhh"),
                    String::from(""),
                    String::from("HHH"),
                    String::from(""),
                    String::from("eee"),
                    String::from(""),
                    String::from("EEE"),
                    String::from(""),
                    String::from("aaa"),
                    String::from(""),
                    String::from("AAA"),
                    String::from(""),
                ];

                let mut proof = test
                    .iter()
                    .map(|x| (x.clone(), x.as_ptr() as usize))
                    .collect::<Vec<(String, usize)>>();

                proof.sort_by_key(|x| x.0.clone());

                let mut orderer = Treerder::new();
                orderer.order(test);

                for zip in proof.iter().zip(test.iter()) {
                    let p = zip.0;
                    let t = zip.1;

                    assert_eq!(&p.0, t); // not necessary, just fancy classic
                    assert_eq!(p.1, t.as_ptr() as usize);
                }
            }
        }

        mod ins {
            use crate::{ab, Alphabet, Treerder};
            use crate::english_letters::ix;

            #[test]
            fn new_path() {
                let entry = "impreciseness";

                let to = Treerder::new();
                let root = &mut ab::<&str>(to.al);
                to_ins(&to, root, &entry);

                let chars: Vec<char> = entry.chars().collect();
                let len = chars.len();
                let last_ix = len - 1;

                let mut sup_ab = &*root;
                for c_ix in 0..len {
                    let c = chars[c_ix];
                    let l = &sup_ab[ix(c)];

                    let terminal_it = c_ix == last_ix;

                    let sub_ab = l.ab.as_ref();
                    assert_eq!(terminal_it, sub_ab.is_none(), "{c_ix}, {c}, {terminal_it}",);

                    if terminal_it {
                        let ens = l.ens.as_ref();
                        assert!(ens.is_some());
                        let ens = ens.unwrap();
                        assert_eq!(1, ens.len());
                        assert_eq!(entry.as_ptr(), ens[0].as_ptr());
                    } else {
                        sup_ab = sub_ab.unwrap();
                    }
                }
            }

            #[test]
            fn double_insert() {
                let entry0 = "impreciseness";
                let entry1 = String::from(entry0);
                let entry2 = String::from(entry0);

                assert_ne!(entry1.as_ptr() as usize, entry2.as_ptr() as usize);

                let to = Treerder::new();
                let root = &mut ab::<&str>(to.al);

                to_ins(&to, root, &*entry1);
                to_ins(&to, root, &*entry2);

                let chars: Vec<char> = entry0.chars().collect();
                let len = chars.len();
                let last_ix = len - 1;

                let mut sup_ab = &*root;
                for c_ix in 0..len {
                    let c = chars[c_ix];
                    let l = &sup_ab[ix(c)];

                    let terminal_it = c_ix == last_ix;

                    let sub_ab = l.ab.as_ref();
                    assert_eq!(terminal_it, sub_ab.is_none(), "{c_ix}, {c}, {terminal_it}");

                    if terminal_it {
                        let ens = l.ens.as_ref();
                        assert!(ens.is_some());
                        let ens = ens.unwrap();
                        assert_eq!(2, ens.len());
                        assert_eq!(entry1.as_ptr(), ens[0].as_ptr());
                        assert_eq!(entry2.as_ptr(), ens[1].as_ptr());
                    } else {
                        sup_ab = sub_ab.unwrap();
                    }
                }
            }

            fn to_ins<'a>(to: &Treerder, ab: &mut Alphabet<&'a str>, e: &'a str) {
                let mut cs = e.chars();
                let c = cs.next().unwrap();

                to.ins(ab, e, c, &mut cs);
            }
        }
    }

    mod readme {
        use crate::{Treerder, Orderable};

        #[test]
        fn test() {
            let mut test_1 = ["zzz", "ZZZ", "aaa", "AAA"];

            let mut test_2 = test_1.map(|x| String::from(x));

            let mut proof = test_1.clone();
            proof.sort();

            let mut orderer = Treerder::new();
            orderer.order(&mut test_1);
            orderer.order(&mut test_2);

            for z in test_1.iter().zip(test_2.iter()) {
                assert_eq!(*z.0, z.1.as_str());
            }

            assert_eq!(proof, test_1);
        }

        #[test]
        fn test2() {
            #[derive(Debug, PartialEq)]
            struct LocalUsize(usize);

            struct LocalUsizeCharIterator {
                s: String,
                c: usize,
            }

            impl Iterator for LocalUsizeCharIterator {
                type Item = char;

                fn next(&mut self) -> Option<char> {
                    let c = self.c;

                    let opt = self.s.chars().nth(c);

                    if opt.is_some() {
                        self.c = c + 1;
                    }

                    opt
                }
            }

            impl Orderable for LocalUsize {
                type Shadow = usize;

                fn chars(&self) -> impl Iterator<Item = char> {
                    LocalUsizeCharIterator {
                        s: self.0.to_string(),
                        c: 0,
                    }
                }

                fn shadow(&self) -> Self::Shadow {
                    self.0
                }

                fn steady(s: Self::Shadow) -> Self {
                    LocalUsize(s)
                }
            }

            fn ix(c: char) -> usize {
                c.to_digit(10).unwrap() as usize
            }

            let mut nums = [999, 333, 33, 3, 0, 100, 10, 1].map(|x| LocalUsize(x));

            let mut orderer = Treerder::new_with(ix, 10);
            orderer.order(&mut nums);

            let proof = [0, 1, 10, 100, 3, 33, 333, 999].map(|x| LocalUsize(x));
            assert_eq!(proof, nums);
        }
    }
}

// cargo test --features test-ext --release
// cargo test --release
