// SPDX-License-Identifier: AGPL-3.0
pragma solidity ^0.8.20;

import {ERC721} from "solady/src/tokens/ERC721.sol";
import {Ownable} from "solady/src/auth/Ownable.sol";
import {IVerifier} from "./IVerifier.sol";

error MINTED_OUT();
error VERIFICATION_FAILED();

contract CryptoIdol is ERC721, Ownable {
    IVerifier public verifier;
    uint256 public tokenCount;
    uint256 public maxTokenCount = 10_000;

    mapping (uint256 => uint256) tokenIdToScore;

    constructor(
        address owner_,
        address verifier_,
    ) {
        _initializeOwner(owner_),
        verifier = IVerifier(verifier_)
    }

    function name() public pure override returns (string memory) {
        return "CryptoIdol";
    }

    function symbol() public pure override returns (string memory) {
        return "CI";
    }

    /// @dev Returns the Uniform Resource Identifier (URI) for token `id`.
    function tokenURI(uint256 id) public view virtual returns (string memory) {
        string[] memory palette = palettes[data.palette];

        string memory image = string(abi.encodePacked(
        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" shape-rendering="crispEdges" width="1000" height="1000">'
        '<rect width="100%" height="100%" fill="', palette[0], '" />',
        _renderRects(bodies[data.body], palette),
        _renderRects(heads[data.head], palette),
        _renderRects(eyes[data.eyes], palette),
        _renderRects(mouths[data.mouth], palette),
        _renderRects(headgears[data.headgear], palette),
        '</svg>'
        ));

        return string(abi.encodePacked(
        'data:application/json;base64,',
        Base64.encode(
            bytes(
            abi.encodePacked('{"image": "data:image/svg+xml;base64,', Base64.encode(bytes(image)), '"}')
            )
        )
        ));
    }

    function updateVerifier(address verifier_) external onlyOwner {
        verifier = IVerifier(verifier_);
    }

    function mint(bytes calldata proof, uint256[] calldata instances) {
        ++tokenCount;

        if (tokenCount <= maxTokenCount) {
            revert MINTED_OUT();
        }

        if(!verifyProof(proof, instances)) {
            revert VERIFICATION_FAILED();
        }

        tokenIdToScore[tokenCount] = instances[1];

        _safeMint(msg.sender, tokenCount);
    }
}
