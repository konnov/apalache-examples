This is a simple specification of a sender-receiver protocol with
acknowledgments.

It demonstrates the use of three tools for TLA<sup>+</sup>:
 - TLC for fast checking of safety and livenss for small parameter values,
 - Apalache for checking safety for larger parameter values with inductive
   invariants and symbolic model checking, and
 - TLAPS for proving safety for all choices of the parameters PAYLOADS and MAX_SEQ.