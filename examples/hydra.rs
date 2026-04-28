//! # Kirby-Paris Hydra
//!
//! A *hydra* is a finite rooted tree. Hercules cuts a leaf. The hydra
//! responds: the parent of the cut leaf grows `n` copies of the rest of
//! the subtree above it (where `n` is the round number, so it grows
//! faster every turn). The game ends when only the root remains.
//!
//! Kirby and Paris (1982) proved Hercules **always wins**, no matter how
//! big the hydra grows. The proof labels each node with an ordinal: the
//! hydra's ordinal is then derived from those labels, and every cut
//! strictly decreases the ordinal. Because ordinals below ε₀ are
//! well-ordered, the descent must terminate.
//!
//! Strikingly, Kirby and Paris also showed this theorem is **independent
//! of Peano Arithmetic** - termination cannot be proved using induction
//! over natural numbers alone. You need the full strength of ordinals
//! up to ε₀.
//!
//! This example does not simulate the full hydra dynamics (the integer
//! state explodes too fast). Instead it shows a small hydra and the
//! ordinal label that proves termination.
//!
//! ## Running
//!
//! ```bash
//! cargo run --example hydra
//! ```

use transfinite::Ordinal;

/// A hydra is a tree where each node has a list of children. We label each
/// node with the ordinal that represents the subtree rooted at that node.
struct Hydra {
    /// Ordinal label of each subtree, ordered from largest to smallest
    /// (matching the CNF convention).
    children: Vec<Hydra>,
}

impl Hydra {
    fn leaf() -> Self {
        Hydra { children: vec![] }
    }

    /// Convert this hydra to its ordinal label.
    ///
    /// A leaf has label 0. An internal node with children labeled
    /// β₁ ≥ β₂ ≥ ... ≥ βₖ has label ω^β₁ + ω^β₂ + ... + ω^βₖ.
    fn to_ordinal(&self) -> Ordinal {
        if self.children.is_empty() {
            return Ordinal::zero();
        }

        // Sort child ordinals descending and accumulate as ω^β_i sum.
        let mut child_ordinals: Vec<Ordinal> = self.children.iter().map(Self::to_ordinal).collect();
        child_ordinals.sort_by(|a, b| b.cmp(a)); // descending

        let mut builder = Ordinal::builder();
        let mut last: Option<Ordinal> = None;
        let mut multiplicity: u32 = 0;

        for beta in child_ordinals {
            if last.as_ref() == Some(&beta) {
                multiplicity += 1;
            } else {
                if let Some(prev) = last {
                    builder = builder.term(prev, multiplicity);
                }
                last = Some(beta);
                multiplicity = 1;
            }
        }
        if let Some(prev) = last {
            builder = builder.term(prev, multiplicity);
        }

        builder.build().expect("CNF terms in decreasing order")
    }
}

fn main() {
    println!("Kirby-Paris Hydra: every cut strictly decreases an ordinal label,");
    println!("and ordinals below ε₀ are well-ordered, so Hercules always wins.\n");

    // Hydra 1: a single edge from root to a leaf.
    //   root - leaf
    // ordinal label: ω^0 = 1.
    let h1 = Hydra {
        children: vec![Hydra::leaf()],
    };
    println!("Hydra 1: root with a single leaf child");
    println!("  ordinal = {}\n", h1.to_ordinal());

    // Hydra 2: root with three leaf children.
    //   root - leaf, leaf, leaf
    // each child labeled 0, so root labeled ω^0 + ω^0 + ω^0 = 3.
    let h2 = Hydra {
        children: (0..3).map(|_| Hydra::leaf()).collect(),
    };
    println!("Hydra 2: root with three leaf children");
    println!("  ordinal = {}\n", h2.to_ordinal());

    // Hydra 3: root - middle - leaf  (a chain of length 2).
    // leaf labeled 0, middle labeled ω^0 = 1, root labeled ω^1 = ω.
    let h3 = Hydra {
        children: vec![Hydra {
            children: vec![Hydra::leaf()],
        }],
    };
    println!("Hydra 3: a chain - root - middle - leaf");
    println!("  ordinal = {}\n", h3.to_ordinal());

    // Hydra 4: root with two children, each itself a chain of length 2.
    //   root
    //   ├── middle - leaf
    //   └── middle - leaf
    // each branch labeled ω, so root labeled ω^ω + ω^ω = ω^ω · 2.
    let h4 = Hydra {
        children: vec![
            Hydra {
                children: vec![Hydra::leaf()],
            },
            Hydra {
                children: vec![Hydra::leaf()],
            },
        ],
    };
    println!("Hydra 4: root with two chain-of-length-2 branches");
    println!("  ordinal = {}\n", h4.to_ordinal());

    // Hydra 5: root with one branch that has a depth-2 chain ending in a leaf.
    //   root
    //   └── middle1
    //       └── middle2 - leaf
    // labels: leaf=0, middle2=ω^0=1, middle1=ω^1=ω, root=ω^ω.
    let h5 = Hydra {
        children: vec![Hydra {
            children: vec![Hydra {
                children: vec![Hydra::leaf()],
            }],
        }],
    };
    println!("Hydra 5: root with a depth-3 chain to a leaf");
    println!("  ordinal = {}\n", h5.to_ordinal());

    println!("Each hydra's ordinal label is its certificate of termination.");
    println!("When Hercules cuts a leaf, the parent grows N copies of the");
    println!("rest of the subtree above it (N = round number). Even though");
    println!("the integer node count explodes, the ordinal label STRICTLY");
    println!("DECREASES. Because there is no infinite descending chain in");
    println!("the ordinals, Hercules wins in finitely many rounds - even");
    println!("though that number can be astronomically larger than anything");
    println!("Peano Arithmetic can express.");
}
