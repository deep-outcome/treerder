use std::vec::Vec;

#[cfg_attr(test, derive(PartialEq))]
struct Letter<'a> {
    #[cfg(test)]
    value: char,
    alphabet: Option<Alphabet<'a>>,
    entries: Option<Entries<'a>>,
}

impl<'a> Letter<'a> {
    fn new() -> Self {
        Letter {
            #[cfg(test)]
            value: '🫀',
            alphabet: None,
            entries: None,
        }
    }
}

type Alphabet<'a> = Box<[Letter<'a>]>;
type Entries<'a> = Vec<&'a str>;

const BASE_ALPHABET_LEN: usize = 26;
const ALPHABET_LEN: usize = BASE_ALPHABET_LEN * 2;

fn alphabet<'a>() -> Alphabet<'a> {
    let mut ab = Vec::with_capacity(ALPHABET_LEN);

    #[cfg(test)]
    let mut c = 'A' as u8;

    for sc in ab.spare_capacity_mut() {
        let mut _letter = sc.write(Letter::new());

        #[cfg(test)]
        {
            _letter.value = c as char;

            if c == 'Z' as u8 {
                c = 'a' as u8;
            } else {
                c = c + 1;
            }
        }
    }

    unsafe { ab.set_len(ALPHABET_LEN) };

    ab.into_boxed_slice()
}

fn ix(c: char) -> usize {
    let code_point = c as usize;

    match code_point {
        | c if c > 64 && c < 91 => c - 'A' as usize,
        | c if c > 96 && c < 123 => c - 'a' as usize + BASE_ALPHABET_LEN,
        | _ => panic!("Unsupported char. Cannot convert to index."),
    }
}

fn exc<'a, 'b>(ab: &'b mut Alphabet<'a>, strs: &mut [&'a str], mut wr_ix: usize) -> usize {
    for letter in ab.iter_mut() {
        if let Some(entries) = letter.entries.as_mut() {
            for e in entries.drain(0..) {
                strs[wr_ix] = e;
                wr_ix += 1;
            }

            letter.entries = None;
        }

        if let Some(alphabet) = letter.alphabet.as_mut() {
            wr_ix = exc(alphabet, strs, wr_ix);
            letter.alphabet = None;
        }
    }

    wr_ix
}

fn ins<'a>(mut ab: &mut Alphabet<'a>, entry: &'a str) {
    let last_letter_ix = entry.len() - 1;

    let mut erator = entry.chars().enumerate();

    loop {
        let (it_ix, c) = erator.next().unwrap();

        let c_ix = ix(c);

        let letter = &mut ab[c_ix];

        if it_ix == last_letter_ix {
            let entries = letter.entries.get_or_insert_with(|| Entries::new());
            entries.push(entry);
            break;
        } else {
            ab = letter.alphabet.get_or_insert_with(|| crate::alphabet())
        }
    }
}

pub struct TrieSorter<'a> {
    root: Alphabet<'a>,
}

impl<'a> TrieSorter<'a> {
    pub fn new() -> Self {
        Self { root: crate::alphabet() }
    }

    /// Suports only A-Za-z `char`s.
    ///
    /// If condition was not upheld, method would unluckily panic.
    ///
    /// Sort is stable.
    pub fn sort(&'a mut self, strs: &mut [&'a str]) {
        let mut wr_ix = 0;

        let root = &mut self.root;
        for ix in 0..strs.len() {
            let curr = strs[ix];

            if curr.len() == 0 {
                strs.swap(wr_ix, ix);
                wr_ix += 1;
            } else {
                ins(root, curr);
            }
        }

        exc(root, strs, wr_ix);
    }
}

#[cfg(test)]
mod tests_of_units {

    use crate::Letter;
    use std::fmt::{Debug, Formatter};
    impl<'a> Debug for Letter<'a> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            let alphabet = some_none(self.alphabet.as_ref());
            let entries = some_none(self.entries.as_ref());

            return f.write_fmt(format_args!(
                "Letter {{\n  value: {:?}\n  alphabet: {}\n  entries: {}\n}}",
                self.value, alphabet, entries
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
            let letter = Letter::new();

            assert_eq!('🫀', letter.value);
            assert!(letter.alphabet.is_none());
            assert!(letter.entries.is_none());
        }
    }

    use super::alphabet as alphabet_fn;

    #[test]
    fn alphabet() {
        let ab = alphabet_fn();
        assert_eq!(crate::ALPHABET_LEN, ab.len());

        let chain = ('A'..='Z').chain('a'..='z');

        for (ix, c) in chain.enumerate() {
            let letter = &ab[ix];

            assert_eq!(c, letter.value);
            assert!(letter.alphabet.is_none());
            assert!(letter.entries.is_none());
        }
    }

    mod ix {
        use crate::ix;
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

    mod exc {
        use crate::{alphabet, exc, ix, Alphabet, Letter};

        #[test]
        fn basic_test() {
            let mut ab = alphabet();

            #[allow(non_snake_case)]
            let A = ["A1", "A2", "A3"];
            let z = ["z1", "z2", "z3"];

            ab[ix('A')].entries = Some(A.to_vec());
            ab[ix('z')].entries = Some(z.to_vec());

            let mut strs = [""; 8];

            let mut offset = 1;
            exc(&mut ab, &mut strs, offset);

            assert_eq!("", strs[0]);

            for s in A.iter().chain(z.iter()) {
                assert_eq!(*s, strs[offset]);
                offset += 1;
            }

            for l in ab.iter() {
                assert!(l.entries.is_none());
            }
        }

        #[test]
        fn nesting() {
            let mut root = alphabet();
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
                assert!(l.entries.is_none());
                assert!(l.alphabet.is_none());
            }

            fn prep<'a, 'b>(ab: &'b mut Alphabet<'a>, ent: &[&'a str], sub_ent: &[&'a str]) {
                let c = ent[0].chars().next().unwrap();
                let sub_c = sub_ent[0].chars().next().unwrap();

                let l = &mut ab[ix(c)];

                let mut l_alphabet = alphabet();
                let sub_l = &mut l_alphabet[ix(sub_c)];
                sub_l.entries = Some(sub_ent.to_vec());

                l.alphabet = Some(l_alphabet);
                l.entries = Some(ent.to_vec());
            }
        }

        #[test]
        #[allow(non_snake_case)]
        fn in_depth_recursion() {
            let mut root = alphabet();
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

            let A = add_ents_to_ab(root, &ordered[0..3]);
            _ = add_ents_to_le(A, &ordered[3..6]);
            let Az = add_ents_to_le(A, &ordered[6..9]);
            let AzB = add_ents_to_le(Az, &ordered[9..12]);
            _ = add_ents_to_le(AzB, &ordered[12..15]);

            let B = add_ents_to_ab(root, &ordered[15..18]);
            _ = add_ents_to_le(B, &ordered[18..21]);

            let y = add_ents_to_ab(root, &ordered[21..24]);
            let yB = add_ents_to_le(y, &ordered[24..27]);
            _ = add_ents_to_le(yB, &ordered[27..30]);
            let yBX = add_ents_to_le(yB, &ordered[30..33]);
            _ = add_ents_to_le(yBX, &ordered[33..36]);

            let mut strs = [""; 36];

            exc(root, &mut strs, 0);

            let mut re_ix = 0;
            for s in ordered.iter() {
                assert_eq!(*s, strs[re_ix]);
                re_ix += 1;
            }

            for l in root.iter() {
                assert!(l.entries.is_none());
                assert!(l.alphabet.is_none());
            }

            fn add_ents_to_le<'a, 'b>(
                le: &'b mut Letter<'a>,
                ent: &[&'a str],
            ) -> &'b mut Letter<'a> {
                let ab = le.alphabet.get_or_insert_with(|| alphabet());
                add_ents_to_ab(ab, ent)
            }

            fn add_ents_to_ab<'a, 'b>(
                ab: &'b mut Alphabet<'a>,
                ent: &[&'a str],
            ) -> &'b mut Letter<'a> {
                let c = ent[0].chars().next().unwrap();
                let l = &mut ab[ix(c)];

                l.entries = Some(ent.to_vec());
                l
            }
        }
    }

    mod ins {
        use crate::{ins, alphabet, ix};

        #[test]
        fn new_path() {
            let mut ab = alphabet();
            let entry = "impreciseness";

            ins(&mut ab, &entry);

            let chars: Vec<char> = entry.chars().collect();
            let len = chars.len();
            let last_ix = len - 1;

            let mut alphabet = &ab;
            for c_ix in 0..len {
                let c = chars[c_ix];
                let l = &alphabet[ix(c)];

                let non_terminal_it = c_ix != last_ix;

                let ab = l.alphabet.as_ref();
                assert_eq!(
                    non_terminal_it,
                    ab.is_some(),
                    "{c_ix}, {c}, {non_terminal_it}",
                );

                if non_terminal_it {
                    alphabet = ab.unwrap();
                } else {
                    let entries = l.entries.as_ref();
                    assert!(entries.is_some());
                    let entries = entries.unwrap();
                    assert_eq!(1, entries.len());
                    assert_eq!(entry, entries[0]);
                    assert!(l.alphabet.is_none());
                }
            }
        }

        #[test]
        fn double_insert() {
            let mut ab = alphabet();
            let entry0 = "impreciseness";
            let entry1 = String::from(entry0);
            let entry2 = String::from(entry0);

            ins(&mut ab, entry1.as_str());
            ins(&mut ab, entry2.as_str());

            let chars: Vec<char> = entry0.chars().collect();
            let len = chars.len();
            let last_ix = len - 1;

            let mut alphabet = &ab;
            for c_ix in 0..len {
                let c = chars[c_ix];
                let l = &alphabet[ix(c)];

                let non_terminal_it = c_ix != last_ix;

                let ab = l.alphabet.as_ref();
                assert_eq!(
                    non_terminal_it,
                    ab.is_some(),
                    "{c_ix}, {c}, {non_terminal_it}"
                );

                if non_terminal_it {
                    alphabet = ab.unwrap();
                } else {
                    let entries = l.entries.as_ref();
                    assert!(entries.is_some());
                    let entries = entries.unwrap();
                    assert_eq!(2, entries.len());
                    assert_eq!(entry1.as_ptr(), entries[0].as_ptr());
                    assert_eq!(entry2.as_ptr(), entries[1].as_ptr());
                }
            }
        }
    }

    mod trie_sorter {
        use crate::{TrieSorter, alphabet};

        #[test]
        fn new() {
            let sorter = TrieSorter::new();
            assert_eq!(alphabet(), sorter.root);
        }

        mod sort {
            use crate::TrieSorter;

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

                let mut sorter = TrieSorter::new();
                sorter.sort(&mut strs);

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

                // strict stability test not possible since all "" point to 0x1
                let emt1 = String::from("");
                let emt2 = String::from("");
                let emt3 = String::new();
                let emt4 = String::new();

                let (a1, a2, a3) = (&*a1, &*a2, &*a3);
                let (b1, b2, b3) = (&*b1, &*b2, &*b3);
                let (emt1, emt2, emt3, emt4) = (&*emt1, &*emt2, &*emt3, &*emt4);

                let mut strs = [emt1, b1, a1, emt2, b2, a2, emt3, b3, a3, emt4];

                let mut sorter = TrieSorter::new();
                sorter.sort(&mut strs);

                #[rustfmt::skip]
                let proof = [
                    emt1, emt2, emt3, emt4,
                    a1, a2, a3,
                    b1, b2, b3,                   
                ];

                for ix in 0..strs.len() {
                    assert_eq!(proof[ix].as_ptr(), strs[ix].as_ptr());
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
                
                
                let proof = [
                    emt1, emt2, emt3,
                    ABC, ABD,
                    INSTANT,
                    JUI, JUN,
                    JUNCTURE, MOMENT,
                    XYA, XYAB, XYABA, XYABC,
                    XYQ, XYZ,
                    abc, abcd, abce,                    
                    abd,
                    percent, percentile,
                    qaa, qrs, qrt, qua,
                    quail, qualification, quality, quantity,                    
                    qwa,
                    xya, xyz,
                    zzaa, zzbb
                ];
                
                let mut sorter = TrieSorter::new();
                sorter.sort(&mut strs);
                
                assert_eq!(proof, strs);
            }
        }
    }
}
