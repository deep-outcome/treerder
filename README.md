# treerder
- retrieval tree orderer
- orders any type implementing `Orderable` trait
- implementation for `&str` and `String` oob
- English alphabet A–Za–z oob

### asymptotic computational complexity

- tc | Ο(s) where s is sum of all `char`s iterated over
- sc | Θ(q) where q is number of unique nodes, i.e. `char`s in respective branches

### basic usage

```rust
let mut test = [
    String::from("zzz"),    
    String::from("ZZZ"),    
    String::from("aaa"),    
    String::from("AAA"),    
];

let mut proof = test.clone();
proof.sort();

let mut orderer = Treerder::new();
orderer.order(&mut test);

assert_eq!(proof, test);
```

### `Orderable` implementation

```rust
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

let mut nums = [9, 8, 7, 5, 3, 1].map(|x| LocalUsize(x));

let mut orderer = Treerder::<LocalUsize>::new_with(ix, ab);
orderer.order(&mut nums);

let proof = [1, 3, 5, 7, 8, 9].map(|x| LocalUsize(x));
assert_eq!(proof, nums);

```
