use treerder::{Orderable, Treerder};

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

#[test]
fn test() {
    let mut nums = localusize(&[999, 333, 33, 3, 0, 100, 10, 1]);

    let mut orderer = Treerder::<LocalUsize>::new_with(ix, 10);
    orderer.order(&mut nums);

    assert_eq!(localusize(&[0, 1, 10, 100, 3, 33, 333, 999]), nums);

    fn localusize(nums: &[usize; 8]) -> [LocalUsize; 8] {
        nums.map(|x| LocalUsize(x))
    }
}
