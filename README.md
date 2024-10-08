# Efficient Apalache

Examples of efficiently using Apalache for model checking TLA<sup>+</sup> and
Quint specifications. If you are looking for general TLA<sup>+</sup> examples,
check [TLA+ Examples][tlaplus-examples].


| Specification | Author       | Customer     | Syntax          | Description |
|---------------|--------------|--------------|-----------------|-------------|
| [Ben-Or 83][] | Igor Konnov  | Fun project  | TLA<sup>+</sup> | Checking safety of Ben-Or's probabilistic consensus that tolerates Byzantine failures. |
| [labyrinth][] | Igor Konnov  | Fun project  | TLA<sup>+</sup> | Simple exploration in a 2D-labyrinth |
| [matter-labs-chonkybft][] | Igor Konnov, Denis Kolegov | Matter Labs | Quint | BFT consensus by Matter Labs |
| [tendermint-accountability][] | Zarko Milosevic, Igor Konnov | Informal Systems | TLA<sup>+</sup> | BFT consensus in Tendermint/CometBFT blockchains |
| [tendermint-light-client][] | Josef Widder, Igor Konnov | Informal Systems | TLA<sup>+</sup> | Light client for Tendermint/CometBFT blockchains |
| [TetraBFT][]  | Giuliano Losa |             | TLA<sup>+</sup> | Checking safety and liveness of TetraBFT consensus |
| [tla-apalache-workshop][] | Igor Konnov et. al. | Informal Systems | TLA<sup>+</sup> | Apalache examples produced when teaching TLA<sup>+</sup> at Informal Systems |
| [zksync-governance][] | Denis Kolegov, Igor Konnov | Matter Labs | Quint | Specification of the ZKsync Governance smart contracts |

**Note:** Whenever a specification cannot be directly included in this
repository, we give proper links to the specifications in the employer's or
customer's GitHub repository.

[Ben-Or 83]: ./ben-or83
[labyrinth]: ./labyrinth
[matter-labs-chonkybft]: ./matter-labs-chonkybft/
[zksync-governance]: ./zksync-governance/
[tendermint-accountability]: ./tendermint-accountability/
[tendermint-light-client]: ./tendermint-light-client/
[TetraBFT]: ./tetra-bft/
[tla-apalache-workshop]: ./tla-apalache-workshop/
[tlaplus-examples]: https://github.com/tlaplus/Examples