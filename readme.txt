Motivations: 
--------------------

Sexplib/typeconv (and binprot) by Jane Street are attractive, but they rely 
on camlp4. I don't like camlp4. I like the metaprogramming facility it
offers but it has many disadvantages. For instance, because the
code is generated on-the-fly, you can not grep for it. Then someone
else look at your code and see a sexp_of_xxx function and has no
idea where this function is. If you have already tried to understand
the source code of ruby on rails, how it works, where stuff are defined, 
then you'll see what I am talking about. Moreover in the past camlp4 has
been "fragile" to evolutions; when a new version of OCaml appeared,
camlp4 sometime broke and you could not compile your code that
was relying on camlp4.

So I've found a in-the-middle solution where I use camlp4 to generate
code (via the small script ocamltarzan.ml), and save the generated code in
a file (e.g test/foo_sexp.ml), which allows then to completely remove
the dependency to camlp4. Once the code has been generated, all
dependencies to camlp4 can be removed. If tomorrow an incompatible new
version of camlp4 arrives (e.g. camlp6 ...), your code will _still_
work, because it does not rely on the new behavior of this camlp4.
It's just regular plain good ocaml code. And you can
grep over code as there is no hidden code somewhere generated on the
fly. All the code is there. You can even use ocamldebug to debug
your generated code. And your original code does not need weird
annotations like TYPE_CONV_XXX that may confuse tool that expect
regular ocaml code. 


Example of use:
---------------

Given a file 'foo.ml' containing a type 't' which you would like to have
'sexp_of_t' and 't_of_sexp' functions, as well as 'sexp_of_tlist' and
'tlist_of_sexp', just add a comment annotation after the types as in:
 
  type t = A | B
    (* with tarzan *)
  type tlist = t list
    (* with tarzan *)

Then use my ocamltarzan (from its source directory) on this file

  $ ./ocamltarzan -choice sexp tests/foo.ml > tests/foo_sexp.ml

The file foo_sexp.ml should now contain the 'xxx_of_sexp' and
'sexp_of_xxx' functions.

To use the new services offered by those functions, you can
write a use_foo.ml file such as: 

  let x = [Foo.A;Foo.A;Foo.B;Foo.A] in
  let sexp = Foo_sexp.sexp_of_tlist x in
  let s = Sexp.to_string_hum sexp (* 'hum' mean human readable *) in
  print_string (s ^ "\n");

  let chan = open_out "out.sexp" in
  output_string chan s;
  close_out chan;

  let sexp2 = Sexp.load_sexp "out.sexp" in
  let x2 = Foo_sexp.tlist_of_sexp sexp2 in
  assert (x = x2);
  ()

This should lead to this output: 
  (A A B A)

Note that once foo_sexp.ml has been generated, the only thing
you really need to compile your code is the lib-sexp/ directory,
which as you can see is a plain regular good ocaml library, 
with no camlp4 stuff involved.

ocamltarzan currently supports multiple code generators, the sexp,
json, value and typeof, visitor, etc. See the pa/ directory.

Pro and cons of tarzan vs jane:
-------------------------------

pro:
 - less camlp4
 - less complicated to build
 - arguably less complicated to use, e.g. no need for the Type_conv_path stuff
   in the ML file
 - better control on the code generation as can easily customize 
   later the generated code, for instance
   to not display certain things in sexp (like the cocci_tag, position, etc)
 - can provide a path for handling different versions, an evolutionnary format
 - easier to debug when there is a problem ...
 - can grep those generated functions; no magic.
 
cons:
 - have to regenerate when change code
 - no Type_conv_path but have to do things manually with some module aliases
 - fragile if change order in .ml ? 


Really in sexplib they put too much things together. First
the lib for just sexp, that could be splitted in its own lib
(like Martin did by splitting json support in json-wheel and json-static)
then the sexp_of, then the of_sexp, then
the fact that their code handle also generation for signatures,
then there is their extensions (sexp_option fields?), and finally that
you need to use camlp4 and put many annotations in your code and to use
ocamlfind in makefile, and -pp, etc.
It makes the barrier of use and understanding higher. It makes
it also hard to extend. If you just want a simple pretty printer
for your data structures, a string_of_xxx, then they ask too much
commitment. I think ocamltarzan is lighter.

Note:
-------
problem with mutually recursive polymorphic. Solution
 - duplicate functions :) have wrap_of_sexp, wrap_of_sexp_2, wrap_of_sexp_3, ...
   as much as needed


Differences with original code:
--------------------------------

Note that among other things, the file pa_sexp_conv.ml is not in the
lib-sexp directory as I include there only the runtime library for
sexp, not the camlp4 stuff.

I put everything in a single package.
I removed packaging stuff; use only one dir.

removed need for findlib
removed OCamlMakefile
removed use of (* pp cpp *); do it manually via special handling
 (fun that they use cpp whereas they claim camplp4 can do everything)
removed need for -pack

num -> nums dependency

See also the modif-orig.txt files in subdirectories.


I have added a pa/pa_visitor.ml to auto generate visitors.


See also pa/modif-orig.txt
