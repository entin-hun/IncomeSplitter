# Config
- clone this repo
- choose which EVM-compatible Blockchain you want to deploy the Solidity contract to, and provide a wallet's private key which has its native token enough for a few transaction into .env , and an JSON_RPC_PROVIDER link.
- in dep+verif.js , customize the array of payees and their shares as needed
- in repo's dir, install [Foundry Forge]([url](https://book.getfoundry.sh/getting-started/installation#using-foundryup))
- command: node dep+verif.js , which for me at the verification step ends with: Error: Failed to get standard json input, but /out/SplitFlattened.sol directory has AutoSplit.json
