# DCHoTT-Agda
Differential cohesion in Homotopy Type Theory by an axiomatized infinitesimal shape modality.
The following is proved and could also be interpreted as theorems about general modalities:

- The formal disk bundle over a group is trivial
- The formal disk bundle over a G-manifold is locally trivial. 
- All F - fiber bundles are associated to an Aut(F) principal bundle.

The only properties we need of a groups are existence of an operation G x G -> G,
a neutral element for this operation without further compatibility requirements and invertibility of all right translations.
[Here](https://dl.dropboxusercontent.com/u/12630719/SchreiberDMV2015b.pdf) (theorem 3.6, 1) and some part of 2) is a short account of the question this code solves.
The classical, category theoretic, version of the theory and together with a lot of opportunities to extend the formalized version is [here](https://arxiv.org/abs/1701.06238).

# State of the code
Notation is not as consequent and compatible with the rest of the HoTT-World as it should be.
This code grew while I was learning homotopy type theory and agda.
This is still witnessed by some stupid definitions for the basic stuff like equivalences and probably some agda-clumsyness.
If you want to have a look at what has been formalized, the following files are probably the right places:

- FormalDiskBundle.agda
- Manifolds.agda
- FiberBundle.agda
- Im.agda

A Modality 'I' is defined in Im.agda in a way similar to the HoTT-Book, 7.7.5.
