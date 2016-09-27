# DCHoTT-Agda
Differential cohesion in Homotopy Type Theory by an axiomatized infinitesimal shape modality. The following is proved:
- The formal disk bundle over a group is trivial
- The formal disk bundle over a G-manifold is locally trivial
An explanation of these notions may be found [here](https://dl.dropboxusercontent.com/u/12630719/SchreiberDMV2015b.pdf) (theorem 3.6, 1) and some part of 2) )


# State of the code
Notation is not as consequent and compatible with the rest of the HoTT-World as it should be.
This code grew while I was learning homotopy type theory and agda.
This is still witness by some stupid definitions for the basic stuff like equivalences and probably some agda-clumsyness.
If you want to have a look at what's been formalized, the following file are the right places:
- FormalDiskBundle.agda
- Manifolds.agda

Some basic properties of left exact Modalities are not proven yet, so there is a bit of cheating in 'Im.agda' i.e., the modality is postulated to commute with the loop space functor.
Furthermore, there is a lot of stuff about pullback squares, which, to my knowledge, has not been formalized in agda before, but probably in coq.

