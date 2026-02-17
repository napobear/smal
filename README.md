# Assemblers and Linkers

*by [https://homepage.cs.uiowa.edu/~dwjones/](Douglas W. Jones)*

*[https://homepage.cs.uiowa.edu/](THE UNIVERSITY OF IOWA Department of Computer Science)*

## Machine Independent SMAL

The machine independent SMAL assembler and linker supports conditional and macro assembly and all linkage editing operations commonly associated with languages such as FORTRAN and C. It comes with a user's manual that also explains how to customize it to support a variety of machine instruction sets.

There are three versions, two written in fairly portable Pascal and one in C. Note that these are old software and have survived many portings to different machines:

* The 16 bit version; [smal.pas](Pascal code) and [smal.txt](user's manual) (plain text format). This supports byte addressing with a 16 bit address space and 16 bit word size.

* 32 bit version A; [smal32.p](Pascal code) and [smal32.me](user's manual) (nroff -me format). This supports word addressing with a 32 bit address space and a 32 bit word size.

* 32 bit version B; [smal32.c](C code) and [smal32/index.html]user's manual (web format). This supports byte addressing with a 32 bit address and and a 32 bit word size.

The paper [SPnE1983assemblyLang.pdf](Assembly Language as Object Code) in Software — Practice and Experience, 1983, describes the core ideas that allow the SMAL assembler to double as a linkage editor for combining assembled object code files.

## Machine Specific versions of SMAL

Various people have customized versions of SMAL for specific machines. The following versions are available here, all in Pascal:

* 6502; [smal6502.p](code) and [smal6502.txt](user's manual) (plain text format).

* 6800; [smalhero.p](code) and [smalhero.me](user's manual) (nroff -me format).

## Other cross development tools

* PDP-8; [ftp://ftp.cs.uiowa.edu/pub/jones/pdp8/pal.c.Z](C code). This largely supports the PAL-8 format documented in DEC's Introduction to Programming, 1973. Gary Messenbrink of Netcom based his [ftp://ftp.cs.uiowa.edu/pub/jones/pdp8/palnet.c.Z](enhanced version) on this to support BART's fleet of PDP-8 systems.

* [pic/index.html](14-bit PIC support tools) are available. These support the PIC16C72, PIC16C73, PIC16C74, PIC16C76, PIC16C77 and several others. The tools include the SMALpic assembler, the SNOPPP PIC programmer, and a Linux driver for the latter. The assembler is derived from the 32-bit SMAL assembler, Version B, listed above.

## Dynamic Linkage

An important feature of Turing-complete computing mechanisms is that they can run programs that generate and run new code. This is both dangerous and essential to the way we use computers. Viruses depend on this, but so do command-language interpreters. The following papers nibble at parts of this problem:

* [SPnE1979programsAs.pdf](Programs as Higher Level Subroutines), Douglas W. Jones, A.B. Baskin, Thomas Chen and Louis Bloomfield, in Software — Practice and Experience, 9 (1979), 149-155.

* [CSC1986dynamic.pdf](Dynamic Binding of Separately Compiled Objects Under Program Control), Rex E. Gantenbein and Douglas W. Jones, Proc. 1986 ACM Computer Science Conference, 287-292.

* [JSysSoft1988dynamic.pdf](The Design and Implementation of a Dynamic Binding Feature for a High-Level Language), Rex E. Gantenbein and Douglas W. Jones, Journal of Systems and Software 8, 4 (Sept. 1988) 259-273.
