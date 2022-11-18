# Imp2MipsCompiler

## Description

This project was part of the compilation course of my master's degree.  
The goal is to compile a toy language we call "Imp" (stand for Imperative) into Mips, an assembly language.__
The main challenge was allocating memory and registers such that we use as few resources as possible. 

### Imp language

Our language includes
- Int
- Variables
- Prints (ASCII number)
- Branchements (If/While)
- Functions with arguments (Calling and Return)
- Basic arithmetic (+, $\times$)

## Translations
- Imp2Mimp : Just some slight changes on the arithmetic to add unitary operations and simplify what we can 
- Mimp2Aimp : Allocation of our instructions into virtual registers (infinite amount)
- Aimp2Eimp : Allocation of our virtual registers into actual registers ($ti, $ai, $v0, and in the stack), check out the file register_allocation.ml to see how it is done (interference graph coloration to use the same register for different variables which do not interfere)
- Eimp2Mips : Translation into assembly language
## How to run

You need to have ocaml and ocamlbuild
- Use `ocamlbuild impc.native` to generate the compiler
- Then use `./impc.native <your .imp file>` to translate it into Mips. It will create several files which are intermediate translations.
- Input the .asm file in [Mars Simulator](http://courses.missouristate.edu/KenVollmar/MARS/), assemble and run !

## License 

Feel free to fork this project as you want.
