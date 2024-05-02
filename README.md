## CryptoIdol Contracts

## Quick Start
The project is built on Foundry


To test
```
forge test
```

Note that the tests generates some test metadata. To decode the base64 strings
```
cd test
python decode_image.py
```


## Addresses
Base

```
CryptoIdolArtExtra.sol
0x2BfB6ADa25f7C3EA1728dA753f6AaBe82aD19cE7

CryptoIdolArt.sol
0x3741f24e8290A72e33B33e84B6141DD82835dfBe

Halo2Verifier.sol
0x129766cB5eA69E7da67b4A3F0E41C78326003A4a

CryptoIdol.sol
0x50A29A9365b21cC1f2D115D1f50873AD906379b8
```

**Foundry is a blazing fast, portable and modular toolkit for Ethereum application development written in Rust.**

Foundry consists of:

-   **Forge**: Ethereum testing framework (like Truffle, Hardhat and DappTools).
-   **Cast**: Swiss army knife for interacting with EVM smart contracts, sending transactions and getting chain data.
-   **Anvil**: Local Ethereum node, akin to Ganache, Hardhat Network.
-   **Chisel**: Fast, utilitarian, and verbose solidity REPL.

## Documentation

https://book.getfoundry.sh/

## Usage

### Build

```shell
$ forge build
```

### Test

```shell
$ forge test
```

### Format

```shell
$ forge fmt
```

### Gas Snapshots

```shell
$ forge snapshot
```

### Anvil

```shell
$ anvil
```

### Deploy

```shell
$ forge script script/Counter.s.sol:CounterScript --rpc-url <your_rpc_url> --private-key <your_private_key>
```

### Cast

```shell
$ cast <subcommand>
```

### Help

```shell
$ forge --help
$ anvil --help
$ cast --help
```
