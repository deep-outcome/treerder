//! Treerder allows for ordering of any type implementing `Orderable`. Oob support for `&str` and `String` and English alphabet A–Za–z.

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
/// optimization by avoiding excesive scenarios like deep cloning and others.
///
/// Check this phantasmal implementation for `usize`.
/// `Orderable` implementation cannot work without providing `Treerder` with
/// appropriate function for alphabet instantiation same as function for `char`
/// index generation. Check `english_letters::ab` and `english_letters::ix`.
/// ```
/// use treerder::{Orderable, Treerder, Alphabet, ab as ab_fn};
///
/// #[derive(Debug, PartialEq)]
/// struct LocalUsize(usize);
///
/// struct LocalUsizeCharIterator {
///     c: char,
///     x: bool,
/// }
///
/// impl Iterator for LocalUsizeCharIterator {
///     type Item = char;
///     
///     fn next(&mut self) -> Option<char> {
///         if self.x {
///             self.x = false;
///             Some(self.c)
///         } else {
///             None
///         }
///     }
/// }
///
/// impl Orderable for LocalUsize {
///     type Shadow = usize;
///     
///     fn chars(&self) -> impl Iterator<Item = char> {
///         let c = self.0.to_string().chars().next().unwrap();
///         LocalUsizeCharIterator { c, x: true }
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
/// fn ab() -> Alphabet<LocalUsize> {
///     ab_fn::<LocalUsize>(10)
/// }
///
/// let mut nums = [9, 8, 7, 5, 3, 1].map(|x| LocalUsize(x));
///
/// let mut orderer = Treerder::<LocalUsize>::new_with(ix, ab);
/// orderer.order(&mut nums);
///
/// let proof = [1, 3, 5, 7, 8, 9].map(|x| LocalUsize(x));
/// assert_eq!(proof, nums);
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
pub struct Letter<T>
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
    fn new() -> Self {
        Letter {
            #[cfg(test)]
            val: '🫀',
            ab: None,
            ens: None,
        }
    }
}

/// Tree node arms. Consists of `Letter`s.
pub type Alphabet<T> = Box<[Letter<T>]>;
/// Index conversion function. Tighten with `Alphabet`.
/// Returns corresponding `usize`d index of `char`.
///
/// For details see `english_letters::ix` implementation.
pub type Ix = fn(char) -> usize;
/// Alphabet function. Constructs alphabet that supports chosen `char`s.
///
/// Not all arms necessarily have to logically exists.
///
/// For details see `english_letters::ab` implementation.
pub type Ab<T> = fn() -> Alphabet<T>;

type Entries<T> = Vec<T>;

/// Alphabet function, tree arms generation of lenght specified.
pub fn ab<T>(len: usize) -> Alphabet<T>
where
    T: Orderable,
{
    let mut ab = Vec::new();
    ab.reserve_exact(len);

    #[cfg(test)]
    #[cfg(feature = "test-ext")]
    let mut c = 'A' as u8;

    for sc in ab.spare_capacity_mut() {
        let mut _letter = sc.write(Letter::new());

        #[cfg(test)]
        #[cfg(feature = "test-ext")]
        {
            _letter.val = c as char;

            if c == 'Z' as u8 {
                c = 'a' as u8;
            } else {
                c = c + 1;
            }
        }
    }

    unsafe { ab.set_len(len) };

    ab.into_boxed_slice()
}

/// Module contains functions for working with English alphabet letters, A-Za-z.
///
/// For details see `Treerder::new_with()`.
pub mod english_letters {

    use crate::{ab as ab_fn, Alphabet, Orderable};

    /// 26
    pub const BASE_ALPHABET_LEN: usize = 26;
    /// 52
    pub const ALPHABET_LEN: usize = BASE_ALPHABET_LEN * 2;

    /// `Alphabet` of English capital and small letters length.
    pub fn ab<T>() -> Alphabet<T>
    where
        T: Orderable,
    {
        ab_fn(ALPHABET_LEN)
    }

    /// Index conversion function.
    pub fn ix(c: char) -> usize {
        let code_point = c as usize;

        match code_point {
            | c if c > 64 && c < 91 => c - 'A' as usize,
            | c if c > 96 && c < 123 => c - 'a' as usize + BASE_ALPHABET_LEN,
            | _ => panic!("Unsupported char. Cannot convert to index."),
        }
    }
}

// TC: Θ(n ⋅ alphabet size + e) ⇒ Θ(n), n = nodes count, e = entries count
fn exc<'b, T>(ab: &'b mut Alphabet<T>, strs: &mut [T], mut wr_ix: usize) -> usize
where
    T: Orderable,
{
    for letter in ab.iter_mut() {
        if let Some(ens) = letter.ens.as_mut() {
            for e in ens.drain(0..) {
                let steady = Orderable::steady(e);
                let some = replace(&mut strs[wr_ix], steady);

                // `Orderable` implementation should bond reconstructed type
                // obligation to be fully-fledged replacement
                // omitting `drop` for any moved-out value is then desirable
                forget(some);

                wr_ix += 1;
            }
            letter.ens = None;
        }

        if let Some(ab) = letter.ab.as_mut() {
            wr_ix = exc(ab, strs, wr_ix);
            letter.ab = None;
        }
    }

    wr_ix
}

/// `Treerder` is coupled with `Orderable`. Enables ordering of any `impl Orderable` type by
/// its `char` sequence representation.
///
/// For details see `fn order`.
pub struct Treerder<T>
where
    T: Orderable,
{
    root: Alphabet<T>,
    ix: Ix,
    ab: Ab<T>,
}

impl<T> Treerder<T>
where
    T: Orderable,
{
    /// Constructs default version of `Treerder`, i.e. via
    /// `fn new_with()` with `english_letters::ab` and `english_letters::ix`.
    pub fn new() -> Self {
        Self::new_with(english_letters::ix, english_letters::ab)
    }

    /// Allows to use custom alphabet different from default alphabet. See `fn new()`.
    ///
    /// For details see implementations of module `english_letters`.
    pub fn new_with(ix: Ix, ab: Ab<T>) -> Self {
        Self { root: ab(), ix, ab }
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
    pub fn order(&mut self, strs: &mut [T]) {
        let mut wr_ix = 0;

        for ix in 0..strs.len() {
            let curr = &strs[ix];
            let mut chars = curr.chars();

            if let Some(c) = chars.next() {
                let shad = curr.shadow();
                self.ins(shad, c, &mut chars);
            } else {
                drop(chars);
                strs.swap(wr_ix, ix);
                wr_ix += 1;
            }
        }

        exc(&mut self.root, strs, wr_ix);
    }

    // TC: Θ(l), l = `cs` length
    // SC: Θ(q ⋅ alphabet size) ⇒ Θ(q) as long as q > alphabet size, q = unique nodes count, [leaf node does not have arms (alphabet)]
    fn ins(&mut self, entry: T::Shadow, mut c: char, cs: &mut impl Iterator<Item = char>) {
        let ix = self.ix;
        let ab = self.ab;

        let mut alphabet = &mut self.root;

        loop {
            let c_ix = ix(c);
            let letter = &mut alphabet[c_ix];

            if let Some(cx) = cs.next() {
                c = cx;
                alphabet = letter.ab.get_or_insert_with(|| ab())
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
        use crate::english_letters::{ab as ab_fn, ALPHABET_LEN};

        #[test]
        fn ab() {
            let ab = ab_fn::<&str>();
            assert_eq!(ALPHABET_LEN, ab.len());
        }

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

                for c in ucs {
                    let result = catch_unwind(|| ix(c));
                    assert!(result.is_err());

                    let err = result.err().unwrap();
                    let downcast = err.downcast_ref::<&str>().unwrap();
                    assert_eq!(&"Unsupported char. Cannot convert to index.", downcast);
                }
            }

            fn unsupported_chars() -> [char; 4] {
                #[rustfmt::skip] let ucs =
                [
                    'A' as u8 -1, 'Z' as u8 +1, // 65–90
                    'a' as u8 -1, 'z' as u8 +1, // 97–122
                ];

                ucs.map(|x| x as char)
            }
        }
    }

    mod exc {
        use crate::{exc, Alphabet, Letter};
        use crate::english_letters::{ab as ab_fn, ix};

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

            for l in ab.iter() {
                assert!(l.ens.is_none());
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

            for l in root.iter() {
                assert!(l.ens.is_none());
                assert!(l.ab.is_none());
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

            for l in root.iter() {
                assert!(l.ens.is_none());
                assert!(l.ab.is_none());
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
    }

    mod treerder {
        use crate::{Treerder, Letter};
        use crate::english_letters::{ix, ab};

        #[test]
        fn new() {
            let orderer = Treerder::<&str>::new();
            assert_eq!(ab(), orderer.root);
            assert_eq!(ab::<&str> as usize, orderer.ab as usize);
            assert_eq!(ix as usize, orderer.ix as usize);
        }

        #[test]
        fn new_with() {
            fn test_ix(_c: char) -> usize {
                0
            }
            fn test_ab() -> Box<[Letter<String>]> {
                Vec::new().into_boxed_slice()
            }

            let orderer = Treerder::<String>::new_with(test_ix, test_ab);

            assert_eq!(test_ab(), orderer.root);
            assert_eq!(test_ab as usize, orderer.ab as usize);
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
            use crate::Treerder;
            use crate::english_letters::ix;

            #[test]
            fn new_path() {
                let entry = "impreciseness";

                let mut to = Treerder::new();
                to_ins(&mut to, &entry);

                let chars: Vec<char> = entry.chars().collect();
                let len = chars.len();
                let last_ix = len - 1;

                let mut sup_ab = &to.root;
                for c_ix in 0..len {
                    let c = chars[c_ix];
                    let l = &sup_ab[ix(c)];

                    let non_terminal_it = c_ix != last_ix;

                    let sub_ab = l.ab.as_ref();
                    assert_eq!(
                        non_terminal_it,
                        sub_ab.is_some(),
                        "{c_ix}, {c}, {non_terminal_it}",
                    );

                    if non_terminal_it {
                        sup_ab = sub_ab.unwrap();
                    } else {
                        let ens = l.ens.as_ref();
                        assert!(ens.is_some());
                        let ens = ens.unwrap();
                        assert_eq!(1, ens.len());
                        assert_eq!(entry.as_ptr(), ens[0].as_ptr());
                        assert!(l.ab.is_none());
                    }
                }
            }

            #[test]
            fn double_insert() {
                let entry0 = "impreciseness";
                let entry1 = String::from(entry0);
                let entry2 = String::from(entry0);

                assert_ne!(entry1.as_ptr() as usize, entry2.as_ptr() as usize);

                let mut to = Treerder::new();
                to_ins(&mut to, &*entry1);
                to_ins(&mut to, &*entry2);

                let chars: Vec<char> = entry0.chars().collect();
                let len = chars.len();
                let last_ix = len - 1;

                let mut sup_ab = &to.root;
                for c_ix in 0..len {
                    let c = chars[c_ix];
                    let l = &sup_ab[ix(c)];

                    let non_terminal_it = c_ix != last_ix;

                    let sub_ab = l.ab.as_ref();
                    assert_eq!(
                        non_terminal_it,
                        sub_ab.is_some(),
                        "{c_ix}, {c}, {non_terminal_it}"
                    );

                    if non_terminal_it {
                        sup_ab = sub_ab.unwrap();
                    } else {
                        let ens = l.ens.as_ref();
                        assert!(ens.is_some());
                        let ens = ens.unwrap();
                        assert_eq!(2, ens.len());
                        assert_eq!(entry1.as_ptr(), ens[0].as_ptr());
                        assert_eq!(entry2.as_ptr(), ens[1].as_ptr());
                    }
                }
            }

            fn to_ins<'a>(to: &mut Treerder<&'a str>, e: &'a str) {
                let mut cs = e.chars();
                let c = cs.next().unwrap();

                to.ins(e, c, &mut cs);
            }
        }
    }
}

// cargo test --features test-ext
