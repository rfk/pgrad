

The plan:  Create a ConGolog system to plan for multiple agents in the
           concurrent, temporal situation calculus with natural actions.
           It will use Prolog's theorem proving to perform regression
           and thus will inherit the closed-world assumption.

           The working name for this language is MConGolog as it will
           inherit the syntax of ConGolog but extend it for the new
           calculus.

           Testing will be based on the "Cooking Agents" domain, where
           several agents cooperate to prepare a meal by executing
           recipies specified as MConGolog programs.


The files:   * sitcalc.pl - foundational axioms of the situation calculus
             * mcongolog.pl - semantics and solver for MConGolog programs
             * domain.pl - axiomatisation of the domain in the calculus
             * main.pl - top-level control file, pulling it all together

