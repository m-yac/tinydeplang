An experiment with implementing a tiny dependently-typed language in Haskell.

I wrote almost all of this while I was bored during OLPSS'17. The next summer I made a few tweaks and started (but never finished) adding quotient inductive-inductive types (see below).

### Notes

- Has a hierarchy of universes a la Russell with universe polymorphism and explicit lifting (i.e. not cumulativity) modeled after that in Agda. (The original 2017 version had cumulative universes and therefore also subtyping -- see commit history!)
- Declarations of inductive-inductive types are supported, but strict positivity checking and pattern matching are not yet implemented. See branch `qiits` for steps towards these things. In fact, that branch has the beginnings of an implementation of *quotient* inductive-inductive types based on that in:

    * Ambrus Kaposi and Andras Kovacs. Codes for quotient inductive inductive types. https://akaposi.github.io/qiit.pdf, 2017.
    * Gabe Dijkstra. Quotient inductive-inductive types. PhD thesis, University of Nottingham, 2017.
    * Thorsten Altenkirch, Paolo Capriotti, Gabe Dijkstra, and Fredrik Nordvall Forsberg. Quotient inductive-inductive types. http://arxiv.org/abs/1612.02346, 2016.  

    For more on what this language supports see the top of `src/Core/Syntax.hs`.
  
- Alpha equivalence and substitution are both handled using a souped-up version of [`bound`](http://hackage.haskell.org/package/bound). Specifically, I changed the definition of `Scope` and added a `Subst` typeclass in order to permit a substitution function with the following type: 

    ```
    subst :: (Subst f g, Eq a) => a -> g a -> f a -> f a
    ```

    where `subst a p w` replaces the free variable `a` with `p` in `w`. Compare this to `bound`'s substitution function, which has the following type:

    ```
    substitute :: (Monad f, Eq a) => a -> f a -> f a -> f a
    ```

    This change was motivated by the fact that I wanted terms and universe variables to have different types, and therefore needed to be able to substitute one universe variable for another in a term. This decision to separate terms and universe variables comes from the fact that it not only cuts out a lot of malformed ASTs, resulting in less cases needed to define typechecking and evaluation (e.g. `evalU` and `eval` in `src/Core/Eval.hs`), but on a moral level, means every term has a type -- while universe levels have no type! The re-definition of `Scope` and all the important `bound` functions are in `src/Utils.hs`. Also see the `INSTANCES` section of `src/Core/Syntax.hs` for a good overview of the typeclasses involved in `bound` and this extension.

- Parsing is done using [`earley`](http://hackage.haskell.org/package/Earley), a monadic Earley parsing library, and tokenization is currently a disaster -- I have no idea why I didn't use a library. (At least I had fun!) See the bottom of `src/Core/Syntax.hs` for the actual parser, and `src/Parser.hs` for helper functions.
- Ambiguities are allowed during parsing, just so long as *exacly one* of the possible parses typechecks (see `resolveAmbig` in `src/Core/Check.hs`). The code for typechecking lives in `src/Core/Check.hs`, and the code for NF and WHNF evaluation is in `src/Core/Eval.hs`.

There is an command-line based interactive interpreter which I implemented using [`haskeline`](http://hackage.haskell.org/package/haskeline). Type `./hom -i` to start this mode -- supported commands are `:q` (quit), `:l` (load file), `:t` (show the type of the given term), and `:d` (show the declaration of the given identifier). Furthermore, entering a well-formed term evaluates it, and entering a well-formed declaration adds it to the ambient context.