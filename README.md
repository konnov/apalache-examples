# Efficient Apalache

Examples of efficiently using Apalache for model checking TLA<sup>+</sup> and
Quint specifications. If you are looking for general TLA<sup>+</sup> examples,
check [TLA+ Examples][tlaplus-examples].


| Specification | Author       | Customer     | Syntax          | Description |
|---------------|--------------|--------------|-----------------|-------------|
| [Ben-Or 83][] | Igor Konnov  | Fun project  | TLA<sup>+</sup> | Probabilistic consensus that tolerates Byzantine failures. We check safety only |
| [labyrinth][] | Igor Konnov  | Fun project  | TLA<sup>+</sup> | Simple exploration in a 2D-labyrinth |
| [matter-labs-chonkybft][] | Igor Konnov, Denis Kolegov | Matter Labs | Quint | BFT consensus by Matter Labs |
| [tendermint-accountability][] | Zarko Milosevic, Igor Konnov | Informal Systems | TLA<sup>+</sup> | BFT consensus in Tendermint/CometBFT blockchains |
| [tendermint-light-client][] | Josef Widder, Igor Konnov | Informal Systems | TLA<sup>+</sup> | Light client for Tendermint/CometBFT blockchains |
| [tla-apalache-workshop][] | Igor Konnov et. al. | Informal Systems | TLA<sup>+</sup> | Apalache examples produced at Informal Systems |
| [zk-governance][] | Denis Kolegov, Igor Konnov | Matter Labs | Quint | Specification of the ZKsync Governance smart contracts |

**Note:** Some of the specifications include open source work by Igor Konnov for
free, as an employee, or as a contractor. In the latter cases, proper links to
the specifications on the employer's/customer's GitHub repository are included.

[Ben-Or 83]: ./ben-or83
[labyrinth]: ./labyrinth
[matter-labs-chonkybft]: ./matter-labs-chonkybft/
[zk-governance]: https://github.com/zksync-association/zk-governance/tree/master/spec
[tendermint-accountability]: ./tendermint-accountability/
[tendermint-light-client]: ./tendermint-light-client/
[tla-apalache-workshop]: ./tla-apalache-workshop/
[tlaplus-examples]: https://github.com/tlaplus/Examples