# treerder
- retrieval tree orderer / ordering based on `char`s sequence representation
- orders any type implementing `Orderable` trait
- implementation for `&str` and `String` oob
- English alphabet A–Za–z oob
- customizable alphabet

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

### `Orderable` implementation with custom alphabet

```rust
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


let mut nums = [999, 333, 33, 3, 0, 100, 10, 1].map(|x| LocalUsize(x));

let mut orderer = Treerder::<LocalUsize>::new_with(ix, 10);
orderer.order(&mut nums);

let proof = [0, 1, 10, 100, 3, 33, 333, 999].map(|x| LocalUsize(x));
assert_eq!(proof, nums);
```
