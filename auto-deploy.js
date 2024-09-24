require("dotenv").config();
const { execSync } = require("child_process");
const fs = require("fs");
const path = require("path");

async function main() {
  // Load environment variables
  const ownerPrivateKey = process.env.OWNER_PRIVATE_KEY;
  const providerURL = process.env.JSON_RPC_PROVIDER;
  const etherscanApiKey = process.env.ETHERSCAN_API_KEY;

  if (!ownerPrivateKey || !providerURL) {
    console.error("Please set OWNER_PRIVATE_KEY and JSON_RPC_PROVIDER in your .env file.");
    process.exit(1);
  }

  // Prepare the payees and shares
  const payees = [
    "0xb75aBb445F7aaae1F2bf09cc4bCFA37371AdE9A0",
    "0xD1771B23ad54292F3b5E4faE2731c6975267d209",
    "0xD1f43Bb785bC124E963Ee62969a2F24Faeb2C606"
  ];
  const shares = [50, 30, 20]; // Ensure this adds up to 100%

  // Convert payees and shares to the format acceptable for forge create
  const payeesArg = payees.join(", ");
  const sharesArg = shares.join(", ");

  // Compile the contract
  console.log("Compiling the contract...");
  execSync("forge build", { stdio: "inherit" });

  // Flatten the contract for verification
  console.log("Flattening the contract...");
  execSync("forge flatten src/AutoSplit.sol > lib/flattened/SplitFlattened.sol", { stdio: "inherit" });
  const flattenedPath = path.join(__dirname, "out", "SplitFlattened.sol");
  if (!fs.existsSync(flattenedPath)) {
    console.error(`Flattened file not found at path: ${flattenedPath}`);
    process.exit(1);
  }

  // Deploy the contract using forge create
  console.log("Deploying the contract...");
  const deployCommand = `forge create --private-key ${ownerPrivateKey} --rpc-url ${providerURL} lib/flattened/SplitFlattened.sol:PaymentSplitter --constructor-args "[${payeesArg}]" "[${sharesArg}]"`;
  const output = execSync(deployCommand, { stdio: "pipe" }).toString();
  console.log(output);

  // Extract deployed contract address from output
  const deployedAddressRegex = /Deployed to: (0x[a-fA-F0-9]{40})/;
  const match = output.match(deployedAddressRegex);
  if (!match) {
    console.error("Failed to extract the deployed contract address.");
    process.exit(1);
  }
  const deployedContractAddress = match[1];
  console.log(`Contract deployed at: ${deployedContractAddress}`);

  // Verify the contract using forge verify-contract
  const verifyCommand = `forge verify-contract --rpc-url ${providerURL} --verifier blockscout --compiler-version 0.8.11 --verifier-url 'https://gnosis-chiado.blockscout.com/api/' ${deployedContractAddress} ${flattenedPath}:AutoSplit`;
  try {
    execSync(verifyCommand, { stdio: "inherit" });
    console.log("Contract verification completed successfully.");
  } catch (err) {
    console.error("Contract verification failed:", err);
    process.exit(1);
  }
}

main().catch((error) => {
  console.error(error);
  process.exit(1);
});