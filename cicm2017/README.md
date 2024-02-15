This is the code accompanying the paper:

- Cezary Kaliszyk and Karol Pąk
  "Presentation and Manipulation of Mizar Properties in an Isabelle Object Logic"
  https://alioth.uwb.edu.pl/~pakkarol/articles/CKKP-CICMMKM17.pdf
  
Like the other files, I have patched them up to be capable of running in
Isabelle2023. I have also included `mizar-cicm2017.tgz` the original
source code.

The relevant parts of the code which would be interesting would be:

- [`Mizar.thy`](./Mizar.thy)
- [`Mizar_Reserve.thy`](./Mizar_Reserve.thy)
- [`Mizar_Defs.thy`](./Mizar_Defs.thy)

I've patched this back up to work with Isabelle-2023.

The code was last modified 30-Mar-2017 07:00 and was compatible with
Isabelle 2016-1.