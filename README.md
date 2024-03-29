This is the formalization of my [article on cartan geometry in modal hott](https://arxiv.org/abs/1806.05966). 
The basis was the formalization of my [thesis](https://ncatlab.org/schreiber/show/thesis+Wellen).
If you want to look at a state compatible with the latter or see other things that have been here earlier,
you can check out the tag 'compatible_with_thesis'.
Everything should check with Agda-2.6.2.2.

# DCHoTT-Agda
Differential cohesion in Homotopy Type Theory by an axiomatized coreduction modality.
This doesn't really require a modal type theory in sense that the rules are different from book-hott, since the coreduction is a monadic modality.

The following is proved and could also be interpreted as theorems about general modalities:

- The formal disk bundle over a group is trivial.
- The formal disk bundle over a V-manifold is locally trivial. 
- All F - fiber bundles are associated to an Aut(F) principal bundle.

In place of groups, a more general structure called homogeneous type is used in the code.
[Here](https://ncatlab.org/schreiber/show/thesis+Wellen) is more information on this project.
[Here](https://dl.dropboxusercontent.com/u/12630719/SchreiberDMV2015b.pdf) (theorem 3.6, 1) and some part of 2) is a short account of the question this code solves.
The classical, category theoretic, version of the theory together with a lot of opportunities to extend the formalized version is [here](https://arxiv.org/abs/1701.06238).

# State of the code
Notation is not as consequent and compatible with the rest of the HoTT-World as it should be.
This code grew while I was learning homotopy type theory and agda.
This is still witnessed by some stupid definitions for the basic stuff like equivalences and probably some agda-clumsyness.
If you want to have a look at what has been formalized, the following files are probably the right places:

- FormalDiskBundle.agda
- Manifolds.agda
- G-structure.agda
- FiberBundle.agda
- Im.agda

A Modality 'I' is defined in Im.agda in a way similar to the HoTT-Book, 7.7.5.
