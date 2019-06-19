Review #14A
===========================================================================

Overall merit
------------
3. Weak accept

Reviewer expertise
------------------
1. No familiarity

Paper summary
-------------
The abstract reports on an Agda formalization of an accounting model for ledgers that underlies many cryptocurrencies.

Comments for author
-------------------
Unfortunately, I have zero experience with blockchain, so I cannot really evaluate the formalism. After some reading on blockchain and UTxO, I still hardly map the Agda code to the concepts I have in mind. I think that a part of the problem is that the text does not explain the code well. For example, what do `R` and `D` parameters mean? From the latter text I guess they have something to do with "redeemer" and 'data", but what are those are not clear as well.

Who is responsible for the correct implementation of the UTxO module? In this case, does the code that type checks as the UTxO module "writes itself", i.e. driven by types, or can errors be made? Is the implementation universal or do different cryptocurrencies have different validators?

When I read "a list of inputs referring to previous outputs", I assumed that the property would be enforced by types in UTxO itself. It was not until the "validity" section when it became clear that the property should be checked separately.

I have experience with Coq but not Agda. I do not know what "<$>" operator does. I can guess judging by types, but it would be nice to have a more detailed explanation of the `utxo` implementation. For instance, does the order of \ and \cup matter (would it be correct to do `utxo l \cup outputs tx \ ...`)?

I think the text would be more understandable if it started with a quick explanation of a ledger and its validity condition (the end of section 2), and then proceeded to formalization.

Also, it was not clear to me which part of the formalization is the base UTxO and which is the extension.


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #14B
===========================================================================

Overall merit
-------------
4. Accept

Reviewer expertise
------------------
2. Some familiarity

Paper summary
-------------
This paper uses dependent types to encode and enforce safety properties for blockchain transactions.

Comments for author
-------------------
This submission is in scope and interesting.

For audience members such as myself with minimal familiarity with blockchain, the talk should be driven by concrete examples of undesirable behaviour prevented by the proposed formalization. Explaining why the behaviour is undesirable and how it is prevented is more important than showing further meta-theoretical results.


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


Review #14C
===========================================================================

Overall merit
-------------
4. Accept

Reviewer expertise
------------------
1. No familiarity

Paper summary
-------------
The purpose of the work is to lay the foundations for a type-driven approach to verification of the UTxO model used in blockchain technology. The authors briefly describe the model by means of transactions and ledgers, and discuss the validity of a transaction with respect to a ledger (this guarantees that ledgers are correct-by-construction). The authors give a discussion on future work.

Comments for author
-------------------
There is still a lot of work to be done in applying formal methods to blockchain technology and I agree with the authors that types can be of great usage. I believe this will be an interesting talk that can give some insights on that.

