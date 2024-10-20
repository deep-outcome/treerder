use treerder::{Orderable, Treerder, Alphabet, ab as ab_fn};

#[derive(Debug, PartialEq)]
struct LocalUsize(usize);

struct LocalUsizeCharIterator {
    c: char,
    x: bool,
}

impl Iterator for LocalUsizeCharIterator {
    type Item = char;

    fn next(&mut self) -> Option<char> {
        if self.x {
            self.x = false;
            Some(self.c)
        } else {
            None
        }
    }
}

impl Orderable for LocalUsize {
    type Shadow = usize;

    fn chars(&self) -> impl Iterator<Item = char> {
        let c = self.0.to_string().chars().next().unwrap();
        LocalUsizeCharIterator { c, x: true }
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

fn ab() -> Alphabet<LocalUsize> {
    ab_fn::<LocalUsize>(10)
}

#[test]
fn test() {
    let mut nums = localusize(&[9, 8, 6, 6, 7, 5, 3, 1]);

    let mut orderer = Treerder::<LocalUsize>::new_with(ix, ab);
    orderer.order(&mut nums);

    assert_eq!(localusize(&[1, 3, 5, 6, 6, 7, 8, 9]), nums);

    fn localusize(nums: &[usize; 8]) -> [LocalUsize; 8] {
        nums.map(|x| LocalUsize(x))
    }
}
