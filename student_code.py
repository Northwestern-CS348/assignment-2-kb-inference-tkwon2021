import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # Student code goes here

        # Fact must be declared in the scope of the entire function to ensure
        # we are always operating on a fact in the KB
        kb_fact = None

        # If fact is a Fact object
        if isinstance(fact, Fact):
            
            # Check if any facts in KB are equal to fact
            for fact_to_retract in self.facts:
                if fact_to_retract == fact:
                    kb_fact = fact_to_retract

                    # If not in KB, return
                    if not kb_fact:
                        return

                    # If a match is found, change the asserted field
                    if len(kb_fact.supported_by) != 0:
                        kb_fact.asserted = False
                        return

                    # If there is no support, then remove the fact from KB
                    elif len(kb_fact.supported_by) == 0:
                        self.facts.remove(kb_fact)
                

        # If rule is a Rule object
        elif isinstance(fact, Rule):

            # Check if any rules in KB are equal to fact
            for fact_to_retract in self.rules:
                if fact_to_retract == fact:
                    kb_fact = fact_to_retract

                    # If not in KB, return 
                    if not kb_fact:
                        return

                    # If there is support for fact, return
                    if len(kb_fact.supported_by) != 0:
                        return

                    # If the fact is asserted, return
                    if kb_fact.asserted:
                        return

                    # If not asserted and no support, remove from KB
                    self.rules.remove(kb_fact)
                
        # Now checking facts that the fact supports
        for supported_fact in kb_fact.supports_facts:
            pair = None

            # Finding a supported_by pair that contains the removed fact
            for fr_pair in supported_fact.supported_by:
                if kb_fact in fr_pair:
                    pair = fr_pair

            # Removing the supported by pair in the facts that were supported by the removed fact
            for fact in self.facts:
                if fact == supported_fact:
                    fact.supported_by.remove(pair)
            
            # Recursive call to make sure all facts that aren't asserted or inferred are removed
            self.kb_retract(supported_fact) 
        

        # Now checking rules that the fact supports
        for supported_rule in kb_fact.supports_rules:
            pair = None

            # Finding a support_by pair that contains the removed fact
            for fr_pair in supported_rule.supported_by:
                if kb_fact in fr_pair:
                    pair = fr_pair

            # Removing the supported_by pair in the rules that were supported by the removed fact
            for rule in self.rules:
                if rule == supported_rule:
                    rule.supported_by.remove(pair)

            # Recursive call to make sure all rules that aren't asserted or inferred are removed
            self.kb_retract(supported_rule)




        

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        # Binding for the fact and the first element of the LHS of the rule
        matchedBinding = match(fact.statement, rule.lhs[0])


        if matchedBinding != False:

            # Check if LHS has only one element; if so, we are asserting a fact
            if len(rule.lhs) == 1:

                # Create the fact using the instantiation of the statment
                f1 = Fact(instantiate(rule.rhs, matchedBinding), [[fact, rule]])
                kb.kb_assert(f1)

                # Add the newly created fact to the supports_fact lists
                fact.supports_facts.append(f1)
                rule.supports_facts.append(f1)
            
            # If more than one element in LHS, we are asserting a rule with
            # rest of the elements of the LHS (exluding the first) as the new
            # LHS
            else :
                lhsList = []

                # Start at 1 since we want to exclude the first elements (element 0)
                for state in rule.lhs[1:]:
                    lhsList.append(instantiate(state, matchedBinding))

                # Create the RHS statement
                rhsStatement = instantiate(rule.rhs, matchedBinding)

                # Create the LHS list (list of statements)
                statementList = [lhsList, rhsStatement]

                # Create the rule using the list of statements we just created
                r1 = Rule(statementList, [[fact, rule]])
                kb.kb_assert(r1)

                # Add the newly created rule to the supports_rule lists
                fact.supports_rules.append(r1)
                rule.supports_rules.append(r1)