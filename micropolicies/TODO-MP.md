* NEXT

(Leo) improve the printing of diffs in registers (calcDiff) in TestHeapSafety

* STACK POLICY

- we finished writing a strawman policy (but not yet property)

- get TestStackSafety minimally compiling

- stack policy should add to depth instead of making fresh colors
  (to avoid polluting rule cache)

- next step: write a simple prop_ in TestStackSafety that just runs the program

- then we need to
  - copy over printing stuff, etc., from TestHeapSafety to TestStackSafety
  - finish writing an example that should pass the policy and try to run it
  - write an example that should NOT pass the policy and try to run it
  - write the property and make sure it makes the right prediction on these two
  - work on generation

- A good next step would be to see if we can debug the following policy
  (similar to one of the ones that was presented to Linton)
     - a location marked in a particular way can only assigned to one time
       (the policy seemed to allow assignments from a particular piece of
       code, but this code itself was not protected)
- related: work on the policies that 

questions to think about
  - should we set up the machine so that the stack can run into the
    heap (to create opportunities for interesting bugs)?

* NOW

beautify the code some more
  use the P monad uniformly for printing, I guess

Find a more permanent fix for the JAL issue
  see the "DPL rules for JAL" email thread

___________________

more permanent fix for the issue with misaligned accesses
  we want a PIPE_trap, not a fatal error

put in a flag controlling whether misaligned accesses are allowed
  and try to discover the bug!

________________________________________________________
* SOON

"JAL r0" is probably bad style (we use it in our first instr)

Falling off the end of memory is not a very interesting behavior --
generate it less often or maybe explicitly look for it and halt
execution

there are too many magic constants saying how many instructions to
generate / execute!

are we generating too many "interesting" immediate fields?

switch to Chris's new syntax for the policy tool when Andrew is ready
  and then
  remove the sed hack in the makefile

________________________________________________________
* LATER

start thinking about stack safety!
  - look at the policy in the draper repo

haskell-mode for emacs!  (on BCP's work laptop)

