// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Halo2Verifier {
    uint256 internal constant    PROOF_LEN_CPTR = 0x44;
    uint256 internal constant        PROOF_CPTR = 0x64;
    uint256 internal constant NUM_INSTANCE_CPTR = 0x16e4;
    uint256 internal constant     INSTANCE_CPTR = 0x1704;

    uint256 internal constant FIRST_QUOTIENT_X_CPTR = 0x09a4;
    uint256 internal constant  LAST_QUOTIENT_X_CPTR = 0x0aa4;

    uint256 internal constant                VK_MPTR = 0x05a0;
    uint256 internal constant         VK_DIGEST_MPTR = 0x05a0;
    uint256 internal constant     NUM_INSTANCES_MPTR = 0x05c0;
    uint256 internal constant                 K_MPTR = 0x05e0;
    uint256 internal constant             N_INV_MPTR = 0x0600;
    uint256 internal constant             OMEGA_MPTR = 0x0620;
    uint256 internal constant         OMEGA_INV_MPTR = 0x0640;
    uint256 internal constant    OMEGA_INV_TO_L_MPTR = 0x0660;
    uint256 internal constant   HAS_ACCUMULATOR_MPTR = 0x0680;
    uint256 internal constant        ACC_OFFSET_MPTR = 0x06a0;
    uint256 internal constant     NUM_ACC_LIMBS_MPTR = 0x06c0;
    uint256 internal constant NUM_ACC_LIMB_BITS_MPTR = 0x06e0;
    uint256 internal constant              G1_X_MPTR = 0x0700;
    uint256 internal constant              G1_Y_MPTR = 0x0720;
    uint256 internal constant            G2_X_1_MPTR = 0x0740;
    uint256 internal constant            G2_X_2_MPTR = 0x0760;
    uint256 internal constant            G2_Y_1_MPTR = 0x0780;
    uint256 internal constant            G2_Y_2_MPTR = 0x07a0;
    uint256 internal constant      NEG_S_G2_X_1_MPTR = 0x07c0;
    uint256 internal constant      NEG_S_G2_X_2_MPTR = 0x07e0;
    uint256 internal constant      NEG_S_G2_Y_1_MPTR = 0x0800;
    uint256 internal constant      NEG_S_G2_Y_2_MPTR = 0x0820;

    uint256 internal constant CHALLENGE_MPTR = 0x1180;

    uint256 internal constant THETA_MPTR = 0x1180;
    uint256 internal constant  BETA_MPTR = 0x11a0;
    uint256 internal constant GAMMA_MPTR = 0x11c0;
    uint256 internal constant     Y_MPTR = 0x11e0;
    uint256 internal constant     X_MPTR = 0x1200;
    uint256 internal constant  ZETA_MPTR = 0x1220;
    uint256 internal constant    NU_MPTR = 0x1240;
    uint256 internal constant    MU_MPTR = 0x1260;

    uint256 internal constant       ACC_LHS_X_MPTR = 0x1280;
    uint256 internal constant       ACC_LHS_Y_MPTR = 0x12a0;
    uint256 internal constant       ACC_RHS_X_MPTR = 0x12c0;
    uint256 internal constant       ACC_RHS_Y_MPTR = 0x12e0;
    uint256 internal constant             X_N_MPTR = 0x1300;
    uint256 internal constant X_N_MINUS_1_INV_MPTR = 0x1320;
    uint256 internal constant          L_LAST_MPTR = 0x1340;
    uint256 internal constant         L_BLIND_MPTR = 0x1360;
    uint256 internal constant             L_0_MPTR = 0x1380;
    uint256 internal constant   INSTANCE_EVAL_MPTR = 0x13a0;
    uint256 internal constant   QUOTIENT_EVAL_MPTR = 0x13c0;
    uint256 internal constant      QUOTIENT_X_MPTR = 0x13e0;
    uint256 internal constant      QUOTIENT_Y_MPTR = 0x1400;
    uint256 internal constant          R_EVAL_MPTR = 0x1420;
    uint256 internal constant   PAIRING_LHS_X_MPTR = 0x1440;
    uint256 internal constant   PAIRING_LHS_Y_MPTR = 0x1460;
    uint256 internal constant   PAIRING_RHS_X_MPTR = 0x1480;
    uint256 internal constant   PAIRING_RHS_Y_MPTR = 0x14a0;

    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) public returns (bool) {
        assembly {
            // Read EC point (x, y) at (proof_cptr, proof_cptr + 0x20),
            // and check if the point is on affine plane,
            // and store them in (hash_mptr, hash_mptr + 0x20).
            // Return updated (success, proof_cptr, hash_mptr).
            function read_ec_point(success, proof_cptr, hash_mptr, q) -> ret0, ret1, ret2 {
                let x := calldataload(proof_cptr)
                let y := calldataload(add(proof_cptr, 0x20))
                ret0 := and(success, lt(x, q))
                ret0 := and(ret0, lt(y, q))
                ret0 := and(ret0, eq(mulmod(y, y, q), addmod(mulmod(x, mulmod(x, x, q), q), 3, q)))
                mstore(hash_mptr, x)
                mstore(add(hash_mptr, 0x20), y)
                ret1 := add(proof_cptr, 0x40)
                ret2 := add(hash_mptr, 0x40)
            }

            // Squeeze challenge by keccak256(memory[0..hash_mptr]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr, hash_mptr).
            function squeeze_challenge(challenge_mptr, hash_mptr, r) -> ret0, ret1 {
                let hash := keccak256(0x00, hash_mptr)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret0 := add(challenge_mptr, 0x20)
                ret1 := 0x20
            }

            // Squeeze challenge without absorbing new input from calldata,
            // by putting an extra 0x01 in memory[0x20] and squeeze by keccak256(memory[0..21]),
            // and store hash mod r as challenge in challenge_mptr,
            // and push back hash in 0x00 as the first input for next squeeze.
            // Return updated (challenge_mptr).
            function squeeze_challenge_cont(challenge_mptr, r) -> ret {
                mstore8(0x20, 0x01)
                let hash := keccak256(0x00, 0x21)
                mstore(challenge_mptr, mod(hash, r))
                mstore(0x00, hash)
                ret := add(challenge_mptr, 0x20)
            }

            // Batch invert values in memory[mptr_start..mptr_end] in place.
            // Return updated (success).
            function batch_invert(success, mptr_start, mptr_end, r) -> ret {
                let gp_mptr := mptr_end
                let gp := mload(mptr_start)
                let mptr := add(mptr_start, 0x20)
                for
                    {}
                    lt(mptr, sub(mptr_end, 0x20))
                    {}
                {
                    gp := mulmod(gp, mload(mptr), r)
                    mstore(gp_mptr, gp)
                    mptr := add(mptr, 0x20)
                    gp_mptr := add(gp_mptr, 0x20)
                }
                gp := mulmod(gp, mload(mptr), r)

                mstore(gp_mptr, 0x20)
                mstore(add(gp_mptr, 0x20), 0x20)
                mstore(add(gp_mptr, 0x40), 0x20)
                mstore(add(gp_mptr, 0x60), gp)
                mstore(add(gp_mptr, 0x80), sub(r, 2))
                mstore(add(gp_mptr, 0xa0), r)
                ret := and(success, staticcall(gas(), 0x05, gp_mptr, 0xc0, gp_mptr, 0x20))
                let all_inv := mload(gp_mptr)

                let first_mptr := mptr_start
                let second_mptr := add(first_mptr, 0x20)
                gp_mptr := sub(gp_mptr, 0x20)
                for
                    {}
                    lt(second_mptr, mptr)
                    {}
                {
                    let inv := mulmod(all_inv, mload(gp_mptr), r)
                    all_inv := mulmod(all_inv, mload(mptr), r)
                    mstore(mptr, inv)
                    mptr := sub(mptr, 0x20)
                    gp_mptr := sub(gp_mptr, 0x20)
                }
                let inv_first := mulmod(all_inv, mload(second_mptr), r)
                let inv_second := mulmod(all_inv, mload(first_mptr), r)
                mstore(first_mptr, inv_first)
                mstore(second_mptr, inv_second)
            }

            // Add (x, y) into point at (0x00, 0x20).
            // Return updated (success).
            function ec_add_acc(success, x, y) -> ret {
                mstore(0x40, x)
                mstore(0x60, y)
                ret := and(success, staticcall(gas(), 0x06, 0x00, 0x80, 0x00, 0x40))
            }

            // Scale point at (0x00, 0x20) by scalar.
            function ec_mul_acc(success, scalar) -> ret {
                mstore(0x40, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x00, 0x60, 0x00, 0x40))
            }

            // Add (x, y) into point at (0x80, 0xa0).
            // Return updated (success).
            function ec_add_tmp(success, x, y) -> ret {
                mstore(0xc0, x)
                mstore(0xe0, y)
                ret := and(success, staticcall(gas(), 0x06, 0x80, 0x80, 0x80, 0x40))
            }

            // Scale point at (0x80, 0xa0) by scalar.
            // Return updated (success).
            function ec_mul_tmp(success, scalar) -> ret {
                mstore(0xc0, scalar)
                ret := and(success, staticcall(gas(), 0x07, 0x80, 0x60, 0x80, 0x40))
            }

            // Perform pairing check.
            // Return updated (success).
            function ec_pairing(success, lhs_x, lhs_y, rhs_x, rhs_y) -> ret {
                mstore(0x00, lhs_x)
                mstore(0x20, lhs_y)
                mstore(0x40, mload(G2_X_1_MPTR))
                mstore(0x60, mload(G2_X_2_MPTR))
                mstore(0x80, mload(G2_Y_1_MPTR))
                mstore(0xa0, mload(G2_Y_2_MPTR))
                mstore(0xc0, rhs_x)
                mstore(0xe0, rhs_y)
                mstore(0x100, mload(NEG_S_G2_X_1_MPTR))
                mstore(0x120, mload(NEG_S_G2_X_2_MPTR))
                mstore(0x140, mload(NEG_S_G2_Y_1_MPTR))
                mstore(0x160, mload(NEG_S_G2_Y_2_MPTR))
                ret := and(success, staticcall(gas(), 0x08, 0x00, 0x180, 0x00, 0x20))
                ret := and(ret, mload(0x00))
            }

            // Modulus
            let q := 21888242871839275222246405745257275088696311157297823662689037894645226208583 // BN254 base field
            let r := 21888242871839275222246405745257275088548364400416034343698204186575808495617 // BN254 scalar field

            // Initialize success as true
            let success := true

            {
                // Load vk_digest and num_instances of vk into memory
                mstore(0x05a0, 0x2181e72a08a81fab2918ddb12e6263a8bd7e0244b8b520b079cbdd9bdd7bc825) // vk_digest
                mstore(0x05c0, 0x0000000000000000000000000000000000000000000000000000000000000001) // num_instances

                // Check valid length of proof
                success := and(success, eq(0x1680, calldataload(PROOF_LEN_CPTR)))

                // Check valid length of instances
                let num_instances := mload(NUM_INSTANCES_MPTR)
                success := and(success, eq(num_instances, calldataload(NUM_INSTANCE_CPTR)))

                // Absorb vk diegst
                mstore(0x00, mload(VK_DIGEST_MPTR))

                // Read instances and witness commitments and generate challenges
                let hash_mptr := 0x20
                let instance_cptr := INSTANCE_CPTR
                for
                    { let instance_cptr_end := add(instance_cptr, mul(0x20, num_instances)) }
                    lt(instance_cptr, instance_cptr_end)
                    {}
                {
                    let instance := calldataload(instance_cptr)
                    success := and(success, lt(instance, r))
                    mstore(hash_mptr, instance)
                    instance_cptr := add(instance_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                let proof_cptr := PROOF_CPTR
                let challenge_mptr := CHALLENGE_MPTR

                // Phase 1
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0240) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 2
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0300) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)

                // Phase 3
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0400) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Phase 4
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0140) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q)
                }

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)

                // Read evaluations
                for
                    { let proof_cptr_end := add(proof_cptr, 0x0b80) }
                    lt(proof_cptr, proof_cptr_end)
                    {}
                {
                    let eval := calldataload(proof_cptr)
                    success := and(success, lt(eval, r))
                    mstore(hash_mptr, eval)
                    proof_cptr := add(proof_cptr, 0x20)
                    hash_mptr := add(hash_mptr, 0x20)
                }

                // Read batch opening proof and generate challenges
                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // zeta
                challenge_mptr := squeeze_challenge_cont(challenge_mptr, r)                        // nu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W

                challenge_mptr, hash_mptr := squeeze_challenge(challenge_mptr, hash_mptr, r)       // mu

                success, proof_cptr, hash_mptr := read_ec_point(success, proof_cptr, hash_mptr, q) // W'

                // Load full vk into memory
                mstore(0x05a0, 0x2181e72a08a81fab2918ddb12e6263a8bd7e0244b8b520b079cbdd9bdd7bc825) // vk_digest
                mstore(0x05c0, 0x0000000000000000000000000000000000000000000000000000000000000001) // num_instances
                mstore(0x05e0, 0x0000000000000000000000000000000000000000000000000000000000000013) // k
                mstore(0x0600, 0x3064486657634403844b0eac78ca882cfd284341fcb0615a15cfcd17b14d8201) // n_inv
                mstore(0x0620, 0x0cf1526aaafac6bacbb67d11a4077806b123f767e4b0883d14cc0193568fc082) // omega
                mstore(0x0640, 0x20784546081c2aba227a9c15990bf6983ba2a2758faf563f38b437203ee230a9) // omega_inv
                mstore(0x0660, 0x230385eb1034f58ed905d7dafbbf62da84661de658f682a719d8836889e04857) // omega_inv_to_l
                mstore(0x0680, 0x0000000000000000000000000000000000000000000000000000000000000000) // has_accumulator
                mstore(0x06a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // acc_offset
                mstore(0x06c0, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limbs
                mstore(0x06e0, 0x0000000000000000000000000000000000000000000000000000000000000000) // num_acc_limb_bits
                mstore(0x0700, 0x0000000000000000000000000000000000000000000000000000000000000001) // g1_x
                mstore(0x0720, 0x0000000000000000000000000000000000000000000000000000000000000002) // g1_y
                mstore(0x0740, 0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2) // g2_x_1
                mstore(0x0760, 0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed) // g2_x_2
                mstore(0x0780, 0x090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b) // g2_y_1
                mstore(0x07a0, 0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa) // g2_y_2
                mstore(0x07c0, 0x186282957db913abd99f91db59fe69922e95040603ef44c0bd7aa3adeef8f5ac) // neg_s_g2_x_1
                mstore(0x07e0, 0x17944351223333f260ddc3b4af45191b856689eda9eab5cbcddbbe570ce860d2) // neg_s_g2_x_2
                mstore(0x0800, 0x06d971ff4a7467c3ec596ed6efc674572e32fd6f52b721f97e35b0b3d3546753) // neg_s_g2_y_1
                mstore(0x0820, 0x06ecdb9f9567f59ed2eee36e1e1d58797fd13cc97fafc2910f5e8a12f202fa9a) // neg_s_g2_y_2
                mstore(0x0840, 0x1028fbe24a0cfa2e6379cba14668a62bc1b89eb47ed490f7f172bf789053a2ac) // fixed_comms[0].x
                mstore(0x0860, 0x08c34bd77bd443acdbfb3777889f677e9e60fc2007da870021d1f214834551e8) // fixed_comms[0].y
                mstore(0x0880, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[1].x
                mstore(0x08a0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[1].y
                mstore(0x08c0, 0x198f5e50d43774efb52504ab406d804dde612e7a187cba0336819cf48e5df364) // fixed_comms[2].x
                mstore(0x08e0, 0x304507577ba983e2fc765330269256126c5f0279916304d4ece2ee02e5b25c6a) // fixed_comms[2].y
                mstore(0x0900, 0x0e5322efe3d4bc78abadb44b958916b624ac0fa4d24747d678fc74e0bceec7ba) // fixed_comms[3].x
                mstore(0x0920, 0x1ffc65268bc1c9a0b808aa2c6936028c0b6c7cb194c747148052ced14425153f) // fixed_comms[3].y
                mstore(0x0940, 0x1ef32e39e102b30addb86cac34eb80d6e17a9743feac7565eeaa3b689e6ec093) // fixed_comms[4].x
                mstore(0x0960, 0x1865f3e9bdacb9735ab6e5dc03060401b29f8eb04c13bfbf6fad0f6decbad2b1) // fixed_comms[4].y
                mstore(0x0980, 0x015ccd350ccce5d5e7f950b330c6f54b8df67486367a70834b4a6f8db14ea9fb) // fixed_comms[5].x
                mstore(0x09a0, 0x140f0c10358102ca6716338ec5c2ecb1c20aa0d82a665bddaea89565a0fdced0) // fixed_comms[5].y
                mstore(0x09c0, 0x2291851f46bdff7b72610f755b5f2f658efd28a4534f0f4629798d9d8b1d635b) // fixed_comms[6].x
                mstore(0x09e0, 0x1e7dbd17fca6ad15c5fdaca8873ed1120e93361480034fdf4f754998e7f18004) // fixed_comms[6].y
                mstore(0x0a00, 0x0f545724efd34fde3edefb77b6aeec7b17f9c72f88aac48f2de2e6d1c3de5b72) // fixed_comms[7].x
                mstore(0x0a20, 0x0670ae99483b8d28ce57ac5f0a8cb8d2dfbf8956b76d8046e8138659119f5515) // fixed_comms[7].y
                mstore(0x0a40, 0x070e0a030f654e686c2a9234f63c77275dea39b50516ca3b48cbb480309b7f43) // fixed_comms[8].x
                mstore(0x0a60, 0x2079d4d692cbc58750a1a5817a1c28514925539c663aaa40675f39774469bf78) // fixed_comms[8].y
                mstore(0x0a80, 0x01cecaa432bebd1e56b8d4d0812625caf680aeeed75a2109f0c831ee193cfdda) // fixed_comms[9].x
                mstore(0x0aa0, 0x156f1989871ac2b3f459a40625b88fe47801742fbbbd3f0755778b9727ab8c93) // fixed_comms[9].y
                mstore(0x0ac0, 0x2e1a0fab888fb2d410fcb03a9cc4c4297449986b411be831c732ede14e30a2c0) // fixed_comms[10].x
                mstore(0x0ae0, 0x1eb778b679b1817e43e034592c5c3a54860d6105256871ec1ed46f968a32341a) // fixed_comms[10].y
                mstore(0x0b00, 0x28ae987f76ec19c761094ed6111bc96e6d4e2db4cbc830deefd9b4c2cc31bd86) // fixed_comms[11].x
                mstore(0x0b20, 0x28f17dffa9dfe7a8d1cc03b64367f9aa0a9adeaf09663930baf55190f20e5ff5) // fixed_comms[11].y
                mstore(0x0b40, 0x21b571c138533e5236e7af470cdf6a7e8e9c8fbfd063fe9b9c5b21d2048c4a8a) // fixed_comms[12].x
                mstore(0x0b60, 0x16f144a6f421f90514f9dd54c19282029c35bfd6775ba57a5e8161e2e7df47d3) // fixed_comms[12].y
                mstore(0x0b80, 0x0c27a19e738ad9d7625b8e55980ed57866553305bde92ada5aef097ce614d57d) // fixed_comms[13].x
                mstore(0x0ba0, 0x2ca24f206fc76c9f5f3605cafc099b0683d75a23f36963b6c10938cc6ad90608) // fixed_comms[13].y
                mstore(0x0bc0, 0x2c0fd6033857724d632f03930b7f1ba7981e235a7e67174cbb97a2cdcc63def9) // fixed_comms[14].x
                mstore(0x0be0, 0x027134ae897584b5a54790b6a8b40c5e1b326ab29075df3e41abe1436ed61e96) // fixed_comms[14].y
                mstore(0x0c00, 0x032047abea5869562c9aa966a76b35892b76ca1c43e24b4393d7b953ac9e575c) // fixed_comms[15].x
                mstore(0x0c20, 0x0cff734387e2b4228f837f1d0a101348b7adbab8928b49dec86e84fb3dc0d674) // fixed_comms[15].y
                mstore(0x0c40, 0x1960c76b0b33856e28700c863f9e09c898836b817768b43ba9aa57e5600f16ca) // fixed_comms[16].x
                mstore(0x0c60, 0x0d0ecd10275dc0e82257f394440871858434acc849bfa30730d8bd7ecc5fd69c) // fixed_comms[16].y
                mstore(0x0c80, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].x
                mstore(0x0ca0, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[17].y
                mstore(0x0cc0, 0x121ad90ac2171bcc15021190c6f5c29bbcc845a1674393bc10fa04cf808a4257) // fixed_comms[18].x
                mstore(0x0ce0, 0x0163b6be96464c22abc59bafec3f677a9ccb6007eb4c5ef8497513021c0b4b5b) // fixed_comms[18].y
                mstore(0x0d00, 0x27c8090b8c167f97c37be1b35aa01d42ab07c33453ce22bf6a3ef63151b4ff56) // fixed_comms[19].x
                mstore(0x0d20, 0x0d9603e94621e25e2395f09bc71894a0b50513add00f006ea7569d61f34fc697) // fixed_comms[19].y
                mstore(0x0d40, 0x2b897474732a15900470b98ba14c7e73750e777474ca72b6205ce4d8fa4d1053) // fixed_comms[20].x
                mstore(0x0d60, 0x01f4920844fa4376eb2658620f8c6ebc22e79b4f63a01bab2f3ff89b1bc6ae9a) // fixed_comms[20].y
                mstore(0x0d80, 0x2a1fa1d0f4eb89f30bfc2b5565b893fe6521d96db256014d92c2a65ca563e333) // fixed_comms[21].x
                mstore(0x0da0, 0x19dba6a7839c48e81a5323bc97059c3362bd08d109ce38fb287ac6ec1e9db43d) // fixed_comms[21].y
                mstore(0x0dc0, 0x2b9d4c5de00c2bd5e59f8686468fe2d29fdcd7662de183a6d27be148e027ab96) // fixed_comms[22].x
                mstore(0x0de0, 0x1635d81017045d1b5681f9f09246329d50bb64bb49d2dc1c60d032e4f93b8de4) // fixed_comms[22].y
                mstore(0x0e00, 0x0f9b9671a7e78dad6cfcb84dba7343ab35c4b7191b3c67f4aba4dccee2bf1d70) // fixed_comms[23].x
                mstore(0x0e20, 0x07db985deefb64a5a83874bd0d4446a6a520e21b982373a7edf5702453320327) // fixed_comms[23].y
                mstore(0x0e40, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[24].x
                mstore(0x0e60, 0x0000000000000000000000000000000000000000000000000000000000000000) // fixed_comms[24].y
                mstore(0x0e80, 0x104f0293494ab4b5d5401bcefc48f8aef5c63030fc78fa5676bfec1f4da954c2) // permutation_comms[0].x
                mstore(0x0ea0, 0x07003db3d2cee2501f56d299315999edd3fec4c037f7f43e359ee21064cfbbb3) // permutation_comms[0].y
                mstore(0x0ec0, 0x03cc7f8efc1f0d2aaa757c5c17aa5a726efd167670d7495ee7f238f297e1bb2d) // permutation_comms[1].x
                mstore(0x0ee0, 0x22836e05f3426f2cd2f01303f32a7095931d7e522613d5bd4eb3922fa070ed5b) // permutation_comms[1].y
                mstore(0x0f00, 0x139de8023ab378e90e646b541a2f8d55b8ba1f5c9105b568d1f72438003a1c8f) // permutation_comms[2].x
                mstore(0x0f20, 0x296615a43062f60451c5d371398899cb08c8d86ffebb7f4dfbc540ea5f199c68) // permutation_comms[2].y
                mstore(0x0f40, 0x26842c57b768d6747b29e1d09dd33739417ea817df071b2db6bd2c20d89e135f) // permutation_comms[3].x
                mstore(0x0f60, 0x18ed596dd5966e5065ddd6ce1f18119a4ce84eb451f6ad4f48f07a8fdc824723) // permutation_comms[3].y
                mstore(0x0f80, 0x1df3edbd699a7a3be57ad88c9db8c3de083d7b3ada6f7668d9bf9a2c7552eba8) // permutation_comms[4].x
                mstore(0x0fa0, 0x2f05af4982d432066a4571f68a3f94b3445ac6409eeafe18a749e8e45c3dafa0) // permutation_comms[4].y
                mstore(0x0fc0, 0x2f0603b6e9614ed48ee9eb37ea7210a4f4d08e669c2d3b7c881278919d921038) // permutation_comms[5].x
                mstore(0x0fe0, 0x0068aa8e233762d850a3eb14a4ea624dfa94f00db59159e418f8018b7de3b8ef) // permutation_comms[5].y
                mstore(0x1000, 0x02b6bd17f87d45f7bfded923fa5be4a99a69ea0b025e7488163e5c1df5a01f70) // permutation_comms[6].x
                mstore(0x1020, 0x0d43522a4734547aebf388df542d3d3e94b726e40a4020e28549c31241b71cc5) // permutation_comms[6].y
                mstore(0x1040, 0x1e1df574c7b338da9243d3a7157820e24ebc5c308a6181df50a10b9e31535839) // permutation_comms[7].x
                mstore(0x1060, 0x134ee8c0360e5e14075b99ce3c9b3fc19dd492dd8fe0e3ada952d0e6e1273e41) // permutation_comms[7].y
                mstore(0x1080, 0x00c82649bafe328038fb870c2e4908f192ed757213cbbed4db7bca878a93809d) // permutation_comms[8].x
                mstore(0x10a0, 0x1868be35ff91d982ddad671e803a76fcce983482c88bca981fbe6ea832958e58) // permutation_comms[8].y
                mstore(0x10c0, 0x2c043ef34496a8f8f4e89fe1aff6a2198077321524e5a898e7419230b47364d0) // permutation_comms[9].x
                mstore(0x10e0, 0x07c614def93aba861db47e3b4ada07fbe7b4301b245e47c51b9a5360126e18fe) // permutation_comms[9].y
                mstore(0x1100, 0x0ee3dc309d0d85d5a05663944e7a6d80e1a84ab895f36ad9cba1d2651475594f) // permutation_comms[10].x
                mstore(0x1120, 0x2a5d96ddb2b557bd21b9341a7d845c49f66b8b838a9254187afbc9bd45b46eba) // permutation_comms[10].y
                mstore(0x1140, 0x0615f01765b394aa21de3de70e3b599d6d6335a25764cec33a3483d1308aa159) // permutation_comms[11].x
                mstore(0x1160, 0x0d2797985b7f8e92d551b95eead9a43f7500e9d9bfcd7bf87eab7bb8a20f36c4) // permutation_comms[11].y

                // Read accumulator from instances
                if mload(HAS_ACCUMULATOR_MPTR) {
                    let num_limbs := mload(NUM_ACC_LIMBS_MPTR)
                    let num_limb_bits := mload(NUM_ACC_LIMB_BITS_MPTR)

                    let cptr := add(INSTANCE_CPTR, mul(mload(ACC_OFFSET_MPTR), 0x20))
                    let lhs_y_off := mul(num_limbs, 0x20)
                    let rhs_x_off := mul(lhs_y_off, 2)
                    let rhs_y_off := mul(lhs_y_off, 3)
                    let lhs_x := calldataload(cptr)
                    let lhs_y := calldataload(add(cptr, lhs_y_off))
                    let rhs_x := calldataload(add(cptr, rhs_x_off))
                    let rhs_y := calldataload(add(cptr, rhs_y_off))
                    for
                        {
                            let cptr_end := add(cptr, mul(0x20, num_limbs))
                            let shift := num_limb_bits
                        }
                        lt(cptr, cptr_end)
                        {}
                    {
                        cptr := add(cptr, 0x20)
                        lhs_x := add(lhs_x, shl(shift, calldataload(cptr)))
                        lhs_y := add(lhs_y, shl(shift, calldataload(add(cptr, lhs_y_off))))
                        rhs_x := add(rhs_x, shl(shift, calldataload(add(cptr, rhs_x_off))))
                        rhs_y := add(rhs_y, shl(shift, calldataload(add(cptr, rhs_y_off))))
                        shift := add(shift, num_limb_bits)
                    }

                    success := and(success, eq(mulmod(lhs_y, lhs_y, q), addmod(mulmod(lhs_x, mulmod(lhs_x, lhs_x, q), q), 3, q)))
                    success := and(success, eq(mulmod(rhs_y, rhs_y, q), addmod(mulmod(rhs_x, mulmod(rhs_x, rhs_x, q), q), 3, q)))

                    mstore(ACC_LHS_X_MPTR, lhs_x)
                    mstore(ACC_LHS_Y_MPTR, lhs_y)
                    mstore(ACC_RHS_X_MPTR, rhs_x)
                    mstore(ACC_RHS_Y_MPTR, rhs_y)
                }

                pop(q)
            }

            // Revert earlier if anything from calldata is invalid
            if iszero(success) {
                revert(0, 0)
            }

            // Compute lagrange evaluations and instance evaluation
            {
                let k := mload(K_MPTR)
                let x := mload(X_MPTR)
                let x_n := x
                for
                    { let idx := 0 }
                    lt(idx, k)
                    { idx := add(idx, 1) }
                {
                    x_n := mulmod(x_n, x_n, r)
                }

                let omega := mload(OMEGA_MPTR)

                let mptr := X_N_MPTR
                let mptr_end := add(mptr, mul(0x20, add(mload(NUM_INSTANCES_MPTR), 6)))
                if iszero(mload(NUM_INSTANCES_MPTR)) {
                    mptr_end := add(mptr_end, 0x20)
                }
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, addmod(x, sub(r, pow_of_omega), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }
                let x_n_minus_1 := addmod(x_n, sub(r, 1), r)
                mstore(mptr_end, x_n_minus_1)
                success := batch_invert(success, X_N_MPTR, add(mptr_end, 0x20), r)

                mptr := X_N_MPTR
                let l_i_common := mulmod(x_n_minus_1, mload(N_INV_MPTR), r)
                for
                    { let pow_of_omega := mload(OMEGA_INV_TO_L_MPTR) }
                    lt(mptr, mptr_end)
                    { mptr := add(mptr, 0x20) }
                {
                    mstore(mptr, mulmod(l_i_common, mulmod(mload(mptr), pow_of_omega, r), r))
                    pow_of_omega := mulmod(pow_of_omega, omega, r)
                }

                let l_blind := mload(add(X_N_MPTR, 0x20))
                let l_i_cptr := add(X_N_MPTR, 0x40)
                for
                    { let l_i_cptr_end := add(X_N_MPTR, 0xc0) }
                    lt(l_i_cptr, l_i_cptr_end)
                    { l_i_cptr := add(l_i_cptr, 0x20) }
                {
                    l_blind := addmod(l_blind, mload(l_i_cptr), r)
                }

                let instance_eval := 0
                for
                    {
                        let instance_cptr := INSTANCE_CPTR
                        let instance_cptr_end := add(instance_cptr, mul(0x20, mload(NUM_INSTANCES_MPTR)))
                    }
                    lt(instance_cptr, instance_cptr_end)
                    {
                        instance_cptr := add(instance_cptr, 0x20)
                        l_i_cptr := add(l_i_cptr, 0x20)
                    }
                {
                    instance_eval := addmod(instance_eval, mulmod(mload(l_i_cptr), calldataload(instance_cptr), r), r)
                }

                let x_n_minus_1_inv := mload(mptr_end)
                let l_last := mload(X_N_MPTR)
                let l_0 := mload(add(X_N_MPTR, 0xc0))

                mstore(X_N_MPTR, x_n)
                mstore(X_N_MINUS_1_INV_MPTR, x_n_minus_1_inv)
                mstore(L_LAST_MPTR, l_last)
                mstore(L_BLIND_MPTR, l_blind)
                mstore(L_0_MPTR, l_0)
                mstore(INSTANCE_EVAL_MPTR, instance_eval)
            }

            // Compute quotient evavluation
            {
                let quotient_eval_numer
                let delta := 4131629893567559867359510883348571134090853742863529169391034518566172092834
                let y := mload(Y_MPTR)
                {
                    let f_21 := calldataload(0x0ec4)
                    let var0 := 0x2
                    let var1 := sub(r, f_21)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_21, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, r)
                    let var9 := mulmod(var6, var8, r)
                    let a_4 := calldataload(0x0b64)
                    let a_0 := calldataload(0x0ae4)
                    let a_2 := calldataload(0x0b24)
                    let var10 := addmod(a_0, a_2, r)
                    let var11 := sub(r, var10)
                    let var12 := addmod(a_4, var11, r)
                    let var13 := mulmod(var9, var12, r)
                    quotient_eval_numer := var13
                }
                {
                    let f_22 := calldataload(0x0ee4)
                    let var0 := 0x2
                    let var1 := sub(r, f_22)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_22, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, r)
                    let var9 := mulmod(var6, var8, r)
                    let a_5 := calldataload(0x0b84)
                    let a_1 := calldataload(0x0b04)
                    let a_3 := calldataload(0x0b44)
                    let var10 := addmod(a_1, a_3, r)
                    let var11 := sub(r, var10)
                    let var12 := addmod(a_5, var11, r)
                    let var13 := mulmod(var9, var12, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_21 := calldataload(0x0ec4)
                    let var0 := 0x1
                    let var1 := sub(r, f_21)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_21, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, r)
                    let var9 := mulmod(var6, var8, r)
                    let a_4 := calldataload(0x0b64)
                    let a_0 := calldataload(0x0ae4)
                    let a_2 := calldataload(0x0b24)
                    let var10 := mulmod(a_0, a_2, r)
                    let var11 := sub(r, var10)
                    let var12 := addmod(a_4, var11, r)
                    let var13 := mulmod(var9, var12, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_22 := calldataload(0x0ee4)
                    let var0 := 0x1
                    let var1 := sub(r, f_22)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_22, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, r)
                    let var9 := mulmod(var6, var8, r)
                    let a_5 := calldataload(0x0b84)
                    let a_1 := calldataload(0x0b04)
                    let a_3 := calldataload(0x0b44)
                    let var10 := mulmod(a_1, a_3, r)
                    let var11 := sub(r, var10)
                    let var12 := addmod(a_5, var11, r)
                    let var13 := mulmod(var9, var12, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_21 := calldataload(0x0ec4)
                    let var0 := 0x1
                    let var1 := sub(r, f_21)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_21, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, r)
                    let var9 := mulmod(var6, var8, r)
                    let a_4 := calldataload(0x0b64)
                    let a_0 := calldataload(0x0ae4)
                    let a_2 := calldataload(0x0b24)
                    let var10 := sub(r, a_2)
                    let var11 := addmod(a_0, var10, r)
                    let var12 := sub(r, var11)
                    let var13 := addmod(a_4, var12, r)
                    let var14 := mulmod(var9, var13, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_22 := calldataload(0x0ee4)
                    let var0 := 0x1
                    let var1 := sub(r, f_22)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_22, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let var7 := 0x4
                    let var8 := addmod(var7, var1, r)
                    let var9 := mulmod(var6, var8, r)
                    let a_5 := calldataload(0x0b84)
                    let a_1 := calldataload(0x0b04)
                    let a_3 := calldataload(0x0b44)
                    let var10 := sub(r, a_3)
                    let var11 := addmod(a_1, var10, r)
                    let var12 := sub(r, var11)
                    let var13 := addmod(a_5, var12, r)
                    let var14 := mulmod(var9, var13, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_21 := calldataload(0x0ec4)
                    let var0 := 0x1
                    let var1 := sub(r, f_21)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_21, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, r)
                    let var9 := mulmod(var6, var8, r)
                    let a_4 := calldataload(0x0b64)
                    let var10 := sub(r, var0)
                    let var11 := addmod(a_4, var10, r)
                    let var12 := mulmod(a_4, var11, r)
                    let var13 := mulmod(var9, var12, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_22 := calldataload(0x0ee4)
                    let var0 := 0x1
                    let var1 := sub(r, f_22)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_22, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let var7 := 0x3
                    let var8 := addmod(var7, var1, r)
                    let var9 := mulmod(var6, var8, r)
                    let a_5 := calldataload(0x0b84)
                    let var10 := sub(r, var0)
                    let var11 := addmod(a_5, var10, r)
                    let var12 := mulmod(a_5, var11, r)
                    let var13 := mulmod(var9, var12, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let f_23 := calldataload(0x0f04)
                    let var0 := 0x1
                    let var1 := sub(r, f_23)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_23, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_4 := calldataload(0x0b64)
                    let a_4_prev_1 := calldataload(0x0c04)
                    let var7 := 0x0
                    let a_0 := calldataload(0x0ae4)
                    let a_2 := calldataload(0x0b24)
                    let var8 := mulmod(a_0, a_2, r)
                    let var9 := addmod(var7, var8, r)
                    let a_1 := calldataload(0x0b04)
                    let a_3 := calldataload(0x0b44)
                    let var10 := mulmod(a_1, a_3, r)
                    let var11 := addmod(var9, var10, r)
                    let var12 := addmod(a_4_prev_1, var11, r)
                    let var13 := sub(r, var12)
                    let var14 := addmod(a_4, var13, r)
                    let var15 := mulmod(var6, var14, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var15, r)
                }
                {
                    let f_23 := calldataload(0x0f04)
                    let var0 := 0x2
                    let var1 := sub(r, f_23)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_23, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_4 := calldataload(0x0b64)
                    let var7 := 0x0
                    let a_0 := calldataload(0x0ae4)
                    let a_2 := calldataload(0x0b24)
                    let var8 := mulmod(a_0, a_2, r)
                    let var9 := addmod(var7, var8, r)
                    let a_1 := calldataload(0x0b04)
                    let a_3 := calldataload(0x0b44)
                    let var10 := mulmod(a_1, a_3, r)
                    let var11 := addmod(var9, var10, r)
                    let var12 := sub(r, var11)
                    let var13 := addmod(a_4, var12, r)
                    let var14 := mulmod(var6, var13, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var14, r)
                }
                {
                    let f_24 := calldataload(0x0f24)
                    let var0 := 0x2
                    let var1 := sub(r, f_24)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_24, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_4 := calldataload(0x0b64)
                    let var7 := 0x1
                    let a_2 := calldataload(0x0b24)
                    let var8 := mulmod(var7, a_2, r)
                    let a_3 := calldataload(0x0b44)
                    let var9 := mulmod(var8, a_3, r)
                    let var10 := sub(r, var9)
                    let var11 := addmod(a_4, var10, r)
                    let var12 := mulmod(var6, var11, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_23 := calldataload(0x0f04)
                    let var0 := 0x1
                    let var1 := sub(r, f_23)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_23, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_4 := calldataload(0x0b64)
                    let a_4_prev_1 := calldataload(0x0c04)
                    let a_2 := calldataload(0x0b24)
                    let var7 := mulmod(var0, a_2, r)
                    let a_3 := calldataload(0x0b44)
                    let var8 := mulmod(var7, a_3, r)
                    let var9 := mulmod(a_4_prev_1, var8, r)
                    let var10 := sub(r, var9)
                    let var11 := addmod(a_4, var10, r)
                    let var12 := mulmod(var6, var11, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_24 := calldataload(0x0f24)
                    let var0 := 0x1
                    let var1 := sub(r, f_24)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_24, var2, r)
                    let var4 := 0x2
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_4 := calldataload(0x0b64)
                    let var7 := 0x0
                    let a_2 := calldataload(0x0b24)
                    let var8 := addmod(var7, a_2, r)
                    let a_3 := calldataload(0x0b44)
                    let var9 := addmod(var8, a_3, r)
                    let var10 := sub(r, var9)
                    let var11 := addmod(a_4, var10, r)
                    let var12 := mulmod(var6, var11, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var12, r)
                }
                {
                    let f_24 := calldataload(0x0f24)
                    let var0 := 0x1
                    let var1 := sub(r, f_24)
                    let var2 := addmod(var0, var1, r)
                    let var3 := mulmod(f_24, var2, r)
                    let var4 := 0x3
                    let var5 := addmod(var4, var1, r)
                    let var6 := mulmod(var3, var5, r)
                    let a_4 := calldataload(0x0b64)
                    let a_4_prev_1 := calldataload(0x0c04)
                    let var7 := 0x0
                    let a_2 := calldataload(0x0b24)
                    let var8 := addmod(var7, a_2, r)
                    let a_3 := calldataload(0x0b44)
                    let var9 := addmod(var8, a_3, r)
                    let var10 := addmod(a_4_prev_1, var9, r)
                    let var11 := sub(r, var10)
                    let var12 := addmod(a_4, var11, r)
                    let var13 := mulmod(var6, var12, r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), var13, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := addmod(l_0, sub(r, mulmod(l_0, calldataload(0x10e4), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let perm_z_last := calldataload(0x11a4)
                    let eval := mulmod(mload(L_LAST_MPTR), addmod(mulmod(perm_z_last, perm_z_last, r), sub(r, perm_z_last), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x1144), sub(r, calldataload(0x1124)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let eval := mulmod(mload(L_0_MPTR), addmod(calldataload(0x11a4), sub(r, calldataload(0x1184)), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x1104)
                    let rhs := calldataload(0x10e4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0ae4), mulmod(beta, calldataload(0x0f64), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0b04), mulmod(beta, calldataload(0x0f84), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0b24), mulmod(beta, calldataload(0x0fa4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0b44), mulmod(beta, calldataload(0x0fc4), r), r), gamma, r), r)
                    mstore(0x00, mulmod(beta, mload(X_MPTR), r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0ae4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0b04), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0b24), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0b44), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x1164)
                    let rhs := calldataload(0x1144)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0b64), mulmod(beta, calldataload(0x0fe4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0b84), mulmod(beta, calldataload(0x1004), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0ba4), mulmod(beta, calldataload(0x1024), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0bc4), mulmod(beta, calldataload(0x1044), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0b64), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0b84), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0ba4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0bc4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let gamma := mload(GAMMA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let lhs := calldataload(0x11c4)
                    let rhs := calldataload(0x11a4)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0be4), mulmod(beta, calldataload(0x1064), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0c24), mulmod(beta, calldataload(0x1084), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(calldataload(0x0c44), mulmod(beta, calldataload(0x10a4), r), r), gamma, r), r)
                    lhs := mulmod(lhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mulmod(beta, calldataload(0x10c4), r), r), gamma, r), r)
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0be4), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0c24), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(calldataload(0x0c44), mload(0x00), r), gamma, r), r)
                    mstore(0x00, mulmod(mload(0x00), delta, r))
                    rhs := mulmod(rhs, addmod(addmod(mload(INSTANCE_EVAL_MPTR), mload(0x00), r), gamma, r), r)
                    let left_sub_right := addmod(lhs, sub(r, rhs), r)
                    let eval := addmod(left_sub_right, sub(r, mulmod(left_sub_right, addmod(mload(L_LAST_MPTR), mload(L_BLIND_MPTR), r), r)), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x11e4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x11e4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_15 := calldataload(0x0e04)
                        let var1 := mulmod(var0, f_15, r)
                        let a_6 := calldataload(0x0ba4)
                        let var2 := mulmod(a_6, f_15, r)
                        let a_7 := calldataload(0x0bc4)
                        let var3 := mulmod(a_7, f_15, r)
                        let a_8 := calldataload(0x0be4)
                        let var4 := mulmod(a_8, f_15, r)
                        table := var1
                        table := addmod(mulmod(table, theta, r), var2, r)
                        table := addmod(mulmod(table, theta, r), var3, r)
                        table := addmod(mulmod(table, theta, r), var4, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_16 := calldataload(0x0e24)
                        let var1 := mulmod(var0, f_16, r)
                        let a_0 := calldataload(0x0ae4)
                        let var2 := mulmod(a_0, f_16, r)
                        let a_2 := calldataload(0x0b24)
                        let var3 := mulmod(a_2, f_16, r)
                        let a_4 := calldataload(0x0b64)
                        let var4 := mulmod(a_4, f_16, r)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, r), var2, r)
                        input_0 := addmod(mulmod(input_0, theta, r), var3, r)
                        input_0 := addmod(mulmod(input_0, theta, r), var4, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x1224), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x1204), sub(r, calldataload(0x11e4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1244), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1244), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_15 := calldataload(0x0e04)
                        let var1 := mulmod(var0, f_15, r)
                        let a_6 := calldataload(0x0ba4)
                        let var2 := mulmod(a_6, f_15, r)
                        let a_7 := calldataload(0x0bc4)
                        let var3 := mulmod(a_7, f_15, r)
                        let a_8 := calldataload(0x0be4)
                        let var4 := mulmod(a_8, f_15, r)
                        table := var1
                        table := addmod(mulmod(table, theta, r), var2, r)
                        table := addmod(mulmod(table, theta, r), var3, r)
                        table := addmod(mulmod(table, theta, r), var4, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_17 := calldataload(0x0e44)
                        let var1 := mulmod(var0, f_17, r)
                        let a_1 := calldataload(0x0b04)
                        let var2 := mulmod(a_1, f_17, r)
                        let a_3 := calldataload(0x0b44)
                        let var3 := mulmod(a_3, f_17, r)
                        let a_5 := calldataload(0x0b84)
                        let var4 := mulmod(a_5, f_17, r)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, r), var2, r)
                        input_0 := addmod(mulmod(input_0, theta, r), var3, r)
                        input_0 := addmod(mulmod(input_0, theta, r), var4, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x1284), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x1264), sub(r, calldataload(0x1244)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x12a4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x12a4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_18 := calldataload(0x0e64)
                        let var1 := mulmod(var0, f_18, r)
                        let a_6 := calldataload(0x0ba4)
                        let var2 := mulmod(a_6, f_18, r)
                        let a_7 := calldataload(0x0bc4)
                        let var3 := mulmod(a_7, f_18, r)
                        table := var1
                        table := addmod(mulmod(table, theta, r), var2, r)
                        table := addmod(mulmod(table, theta, r), var3, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_19 := calldataload(0x0e84)
                        let var1 := mulmod(var0, f_19, r)
                        let a_0 := calldataload(0x0ae4)
                        let var2 := mulmod(a_0, f_19, r)
                        let a_2 := calldataload(0x0b24)
                        let var3 := mulmod(a_2, f_19, r)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, r), var2, r)
                        input_0 := addmod(mulmod(input_0, theta, r), var3, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x12e4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x12c4), sub(r, calldataload(0x12a4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1304), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1304), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let var0 := 0x1
                        let f_18 := calldataload(0x0e64)
                        let var1 := mulmod(var0, f_18, r)
                        let a_6 := calldataload(0x0ba4)
                        let var2 := mulmod(a_6, f_18, r)
                        let a_7 := calldataload(0x0bc4)
                        let var3 := mulmod(a_7, f_18, r)
                        table := var1
                        table := addmod(mulmod(table, theta, r), var2, r)
                        table := addmod(mulmod(table, theta, r), var3, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let var0 := 0x1
                        let f_20 := calldataload(0x0ea4)
                        let var1 := mulmod(var0, f_20, r)
                        let a_1 := calldataload(0x0b04)
                        let var2 := mulmod(a_1, f_20, r)
                        let a_3 := calldataload(0x0b44)
                        let var3 := mulmod(a_3, f_20, r)
                        input_0 := var1
                        input_0 := addmod(mulmod(input_0, theta, r), var2, r)
                        input_0 := addmod(mulmod(input_0, theta, r), var3, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x1344), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x1324), sub(r, calldataload(0x1304)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1364), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1364), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x0c64)
                        let f_3 := calldataload(0x0c84)
                        table := f_2
                        table := addmod(mulmod(table, theta, r), f_3, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_7 := calldataload(0x0d04)
                        let var0 := 0x1
                        let var1 := mulmod(f_7, var0, r)
                        let a_0 := calldataload(0x0ae4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effc3ad3
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_4 := calldataload(0x0b64)
                        let var8 := mulmod(var1, a_4, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x13a4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x1384), sub(r, calldataload(0x1364)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x13c4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x13c4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x0c64)
                        let f_3 := calldataload(0x0c84)
                        table := f_2
                        table := addmod(mulmod(table, theta, r), f_3, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_8 := calldataload(0x0d24)
                        let var0 := 0x1
                        let var1 := mulmod(f_8, var0, r)
                        let a_1 := calldataload(0x0b04)
                        let var2 := mulmod(var1, a_1, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effc3ad3
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_5 := calldataload(0x0b84)
                        let var8 := mulmod(var1, a_5, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x1404), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x13e4), sub(r, calldataload(0x13c4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1424), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1424), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x0c64)
                        let f_4 := calldataload(0x0ca4)
                        table := f_2
                        table := addmod(mulmod(table, theta, r), f_4, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_9 := calldataload(0x0d44)
                        let var0 := 0x1
                        let var1 := mulmod(f_9, var0, r)
                        let a_0 := calldataload(0x0ae4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effc3ad3
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_4 := calldataload(0x0b64)
                        let var8 := mulmod(var1, a_4, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x1464), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x1444), sub(r, calldataload(0x1424)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1484), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1484), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x0c64)
                        let f_4 := calldataload(0x0ca4)
                        table := f_2
                        table := addmod(mulmod(table, theta, r), f_4, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_10 := calldataload(0x0d64)
                        let var0 := 0x1
                        let var1 := mulmod(f_10, var0, r)
                        let a_1 := calldataload(0x0b04)
                        let var2 := mulmod(var1, a_1, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effc3ad3
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_5 := calldataload(0x0b84)
                        let var8 := mulmod(var1, a_5, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x14c4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x14a4), sub(r, calldataload(0x1484)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x14e4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x14e4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x0c64)
                        let f_5 := calldataload(0x0cc4)
                        table := f_2
                        table := addmod(mulmod(table, theta, r), f_5, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_11 := calldataload(0x0d84)
                        let var0 := 0x1
                        let var1 := mulmod(f_11, var0, r)
                        let a_0 := calldataload(0x0ae4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effc3ad3
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_4 := calldataload(0x0b64)
                        let var8 := mulmod(var1, a_4, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x1524), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x1504), sub(r, calldataload(0x14e4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1544), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1544), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_2 := calldataload(0x0c64)
                        let f_5 := calldataload(0x0cc4)
                        table := f_2
                        table := addmod(mulmod(table, theta, r), f_5, r)
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_12 := calldataload(0x0da4)
                        let var0 := 0x1
                        let var1 := mulmod(f_12, var0, r)
                        let a_1 := calldataload(0x0b04)
                        let var2 := mulmod(var1, a_1, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effc3ad3
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        let a_5 := calldataload(0x0b84)
                        let var8 := mulmod(var1, a_5, r)
                        let var9 := 0x0
                        let var10 := mulmod(var4, var9, r)
                        let var11 := addmod(var8, var10, r)
                        input_0 := var7
                        input_0 := addmod(mulmod(input_0, theta, r), var11, r)
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x1584), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x1564), sub(r, calldataload(0x1544)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x15a4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x15a4), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_6 := calldataload(0x0ce4)
                        table := f_6
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_13 := calldataload(0x0dc4)
                        let var0 := 0x1
                        let var1 := mulmod(f_13, var0, r)
                        let a_0 := calldataload(0x0ae4)
                        let var2 := mulmod(var1, a_0, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff001
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x15e4), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x15c4), sub(r, calldataload(0x15a4)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_0 := mload(L_0_MPTR)
                    let eval := mulmod(l_0, calldataload(0x1604), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let l_last := mload(L_LAST_MPTR)
                    let eval := mulmod(l_last, calldataload(0x1604), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }
                {
                    let theta := mload(THETA_MPTR)
                    let beta := mload(BETA_MPTR)
                    let table
                    {
                        let f_6 := calldataload(0x0ce4)
                        table := f_6
                        table := addmod(table, beta, r)
                    }
                    let input_0
                    {
                        let f_14 := calldataload(0x0de4)
                        let var0 := 0x1
                        let var1 := mulmod(f_14, var0, r)
                        let a_1 := calldataload(0x0b04)
                        let var2 := mulmod(var1, a_1, r)
                        let var3 := sub(r, var1)
                        let var4 := addmod(var0, var3, r)
                        let var5 := 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff001
                        let var6 := mulmod(var4, var5, r)
                        let var7 := addmod(var2, var6, r)
                        input_0 := var7
                        input_0 := addmod(input_0, beta, r)
                    }
                    let lhs
                    let rhs
                    rhs := table
                    {
                        let tmp := input_0
                        rhs := addmod(rhs, sub(r, mulmod(calldataload(0x1644), tmp, r)), r)
                        lhs := mulmod(mulmod(table, tmp, r), addmod(calldataload(0x1624), sub(r, calldataload(0x1604)), r), r)
                    }
                    let eval := mulmod(addmod(1, sub(r, addmod(mload(L_BLIND_MPTR), mload(L_LAST_MPTR), r)), r), addmod(lhs, sub(r, rhs), r), r)
                    quotient_eval_numer := addmod(mulmod(quotient_eval_numer, y, r), eval, r)
                }

                pop(y)
                pop(delta)

                let quotient_eval := mulmod(quotient_eval_numer, mload(X_N_MINUS_1_INV_MPTR), r)
                mstore(QUOTIENT_EVAL_MPTR, quotient_eval)
            }

            // Compute quotient commitment
            {
                mstore(0x00, calldataload(LAST_QUOTIENT_X_CPTR))
                mstore(0x20, calldataload(add(LAST_QUOTIENT_X_CPTR, 0x20)))
                let x_n := mload(X_N_MPTR)
                for
                    {
                        let cptr := sub(LAST_QUOTIENT_X_CPTR, 0x40)
                        let cptr_end := sub(FIRST_QUOTIENT_X_CPTR, 0x40)
                    }
                    lt(cptr_end, cptr)
                    {}
                {
                    success := ec_mul_acc(success, x_n)
                    success := ec_add_acc(success, calldataload(cptr), calldataload(add(cptr, 0x20)))
                    cptr := sub(cptr, 0x40)
                }
                mstore(QUOTIENT_X_MPTR, mload(0x00))
                mstore(QUOTIENT_Y_MPTR, mload(0x20))
            }

            // Compute pairing lhs and rhs
            {
                {
                    let x := mload(X_MPTR)
                    let omega := mload(OMEGA_MPTR)
                    let omega_inv := mload(OMEGA_INV_MPTR)
                    let x_pow_of_omega := mulmod(x, omega, r)
                    mstore(0x0360, x_pow_of_omega)
                    mstore(0x0340, x)
                    x_pow_of_omega := mulmod(x, omega_inv, r)
                    mstore(0x0320, x_pow_of_omega)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    x_pow_of_omega := mulmod(x_pow_of_omega, omega_inv, r)
                    mstore(0x0300, x_pow_of_omega)
                }
                {
                    let mu := mload(MU_MPTR)
                    for
                        {
                            let mptr := 0x0380
                            let mptr_end := 0x0400
                            let point_mptr := 0x0300
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            point_mptr := add(point_mptr, 0x20)
                        }
                    {
                        mstore(mptr, addmod(mu, sub(r, mload(point_mptr)), r))
                    }
                    let s
                    s := mload(0x03c0)
                    mstore(0x0400, s)
                    let diff
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), r)
                    diff := mulmod(diff, mload(0x03e0), r)
                    mstore(0x0420, diff)
                    mstore(0x00, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03e0), r)
                    mstore(0x0440, diff)
                    diff := mload(0x03a0)
                    mstore(0x0460, diff)
                    diff := mload(0x0380)
                    diff := mulmod(diff, mload(0x03a0), r)
                    mstore(0x0480, diff)
                }
                {
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := 1
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0x20, coeff)
                }
                {
                    let point_1 := mload(0x0320)
                    let point_2 := mload(0x0340)
                    let coeff
                    coeff := addmod(point_1, sub(r, point_2), r)
                    coeff := mulmod(coeff, mload(0x03a0), r)
                    mstore(0x40, coeff)
                    coeff := addmod(point_2, sub(r, point_1), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0x60, coeff)
                }
                {
                    let point_0 := mload(0x0300)
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_0, sub(r, point_2), r)
                    coeff := mulmod(coeff, addmod(point_0, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x0380), r)
                    mstore(0x80, coeff)
                    coeff := addmod(point_2, sub(r, point_0), r)
                    coeff := mulmod(coeff, addmod(point_2, sub(r, point_3), r), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0xa0, coeff)
                    coeff := addmod(point_3, sub(r, point_0), r)
                    coeff := mulmod(coeff, addmod(point_3, sub(r, point_2), r), r)
                    coeff := mulmod(coeff, mload(0x03e0), r)
                    mstore(0xc0, coeff)
                }
                {
                    let point_2 := mload(0x0340)
                    let point_3 := mload(0x0360)
                    let coeff
                    coeff := addmod(point_2, sub(r, point_3), r)
                    coeff := mulmod(coeff, mload(0x03c0), r)
                    mstore(0xe0, coeff)
                    coeff := addmod(point_3, sub(r, point_2), r)
                    coeff := mulmod(coeff, mload(0x03e0), r)
                    mstore(0x0100, coeff)
                }
                {
                    success := batch_invert(success, 0, 0x0120, r)
                    let diff_0_inv := mload(0x00)
                    mstore(0x0420, diff_0_inv)
                    for
                        {
                            let mptr := 0x0440
                            let mptr_end := 0x04a0
                        }
                        lt(mptr, mptr_end)
                        { mptr := add(mptr, 0x20) }
                    {
                        mstore(mptr, mulmod(mload(mptr), diff_0_inv, r))
                    }
                }
                {
                    let coeff := mload(0x20)
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x0f44), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, mload(QUOTIENT_EVAL_MPTR), r), r)
                    for
                        {
                            let mptr := 0x10c4
                            let mptr_end := 0x0f44
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    for
                        {
                            let mptr := 0x0f24
                            let mptr_end := 0x0c04
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1644), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x15e4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1584), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1524), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x14c4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1464), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1404), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x13a4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1344), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x12e4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1284), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(coeff, calldataload(0x1224), r), r)
                    for
                        {
                            let mptr := 0x0be4
                            let mptr_end := 0x0b64
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    for
                        {
                            let mptr := 0x0b44
                            let mptr_end := 0x0ac4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x20) }
                    {
                        r_eval := addmod(mulmod(r_eval, zeta, r), mulmod(coeff, calldataload(mptr), r), r)
                    }
                    mstore(0x04a0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x40), calldataload(0x0c04), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x60), calldataload(0x0b64), r), r)
                    r_eval := mulmod(r_eval, mload(0x0440), r)
                    mstore(0x04c0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x1184), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x1144), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x1164), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0x80), calldataload(0x1124), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xa0), calldataload(0x10e4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0xc0), calldataload(0x1104), r), r)
                    r_eval := mulmod(r_eval, mload(0x0460), r)
                    mstore(0x04e0, r_eval)
                }
                {
                    let zeta := mload(ZETA_MPTR)
                    let r_eval := 0
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x1604), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1624), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x15a4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x15c4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x1544), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1564), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x14e4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1504), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x1484), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x14a4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x1424), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1444), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x13c4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x13e4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x1364), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1384), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x1304), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1324), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x12a4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x12c4), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x1244), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1264), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x11e4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x1204), r), r)
                    r_eval := mulmod(r_eval, zeta, r)
                    r_eval := addmod(r_eval, mulmod(mload(0xe0), calldataload(0x11a4), r), r)
                    r_eval := addmod(r_eval, mulmod(mload(0x0100), calldataload(0x11c4), r), r)
                    r_eval := mulmod(r_eval, mload(0x0480), r)
                    mstore(0x0500, r_eval)
                }
                {
                    let sum := mload(0x20)
                    mstore(0x0520, sum)
                }
                {
                    let sum := mload(0x40)
                    sum := addmod(sum, mload(0x60), r)
                    mstore(0x0540, sum)
                }
                {
                    let sum := mload(0x80)
                    sum := addmod(sum, mload(0xa0), r)
                    sum := addmod(sum, mload(0xc0), r)
                    mstore(0x0560, sum)
                }
                {
                    let sum := mload(0xe0)
                    sum := addmod(sum, mload(0x0100), r)
                    mstore(0x0580, sum)
                }
                {
                    for
                        {
                            let mptr := 0x00
                            let mptr_end := 0x80
                            let sum_mptr := 0x0520
                        }
                        lt(mptr, mptr_end)
                        {
                            mptr := add(mptr, 0x20)
                            sum_mptr := add(sum_mptr, 0x20)
                        }
                    {
                        mstore(mptr, mload(sum_mptr))
                    }
                    success := batch_invert(success, 0, 0x80, r)
                    let r_eval := mulmod(mload(0x60), mload(0x0500), r)
                    for
                        {
                            let sum_inv_mptr := 0x40
                            let sum_inv_mptr_end := 0x80
                            let r_eval_mptr := 0x04e0
                        }
                        lt(sum_inv_mptr, sum_inv_mptr_end)
                        {
                            sum_inv_mptr := sub(sum_inv_mptr, 0x20)
                            r_eval_mptr := sub(r_eval_mptr, 0x20)
                        }
                    {
                        r_eval := mulmod(r_eval, mload(NU_MPTR), r)
                        r_eval := addmod(r_eval, mulmod(mload(sum_inv_mptr), mload(r_eval_mptr), r), r)
                    }
                    mstore(R_EVAL_MPTR, r_eval)
                }
                {
                    let nu := mload(NU_MPTR)
                    mstore(0x00, calldataload(0x0964))
                    mstore(0x20, calldataload(0x0984))
                    success := ec_mul_acc(success, mload(ZETA_MPTR))
                    success := ec_add_acc(success, mload(QUOTIENT_X_MPTR), mload(QUOTIENT_Y_MPTR))
                    for
                        {
                            let mptr := 0x1140
                            let mptr_end := 0x0800
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, mload(mptr), mload(add(mptr, 0x20)))
                    }
                    for
                        {
                            let mptr := 0x0564
                            let mptr_end := 0x0164
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    for
                        {
                            let mptr := 0x0124
                            let mptr_end := 0x24
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_acc(success, mload(ZETA_MPTR))
                        success := ec_add_acc(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    mstore(0x80, calldataload(0x0164))
                    mstore(0xa0, calldataload(0x0184))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0440), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), r)
                    mstore(0x80, calldataload(0x05e4))
                    mstore(0xa0, calldataload(0x0604))
                    success := ec_mul_tmp(success, mload(ZETA_MPTR))
                    success := ec_add_tmp(success, calldataload(0x05a4), calldataload(0x05c4))
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0460), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    nu := mulmod(nu, mload(NU_MPTR), r)
                    mstore(0x80, calldataload(0x0924))
                    mstore(0xa0, calldataload(0x0944))
                    for
                        {
                            let mptr := 0x08e4
                            let mptr_end := 0x05e4
                        }
                        lt(mptr_end, mptr)
                        { mptr := sub(mptr, 0x40) }
                    {
                        success := ec_mul_tmp(success, mload(ZETA_MPTR))
                        success := ec_add_tmp(success, calldataload(mptr), calldataload(add(mptr, 0x20)))
                    }
                    success := ec_mul_tmp(success, mulmod(nu, mload(0x0480), r))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, mload(G1_X_MPTR))
                    mstore(0xa0, mload(G1_Y_MPTR))
                    success := ec_mul_tmp(success, sub(r, mload(R_EVAL_MPTR)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x1664))
                    mstore(0xa0, calldataload(0x1684))
                    success := ec_mul_tmp(success, sub(r, mload(0x0400)))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(0x80, calldataload(0x16a4))
                    mstore(0xa0, calldataload(0x16c4))
                    success := ec_mul_tmp(success, mload(MU_MPTR))
                    success := ec_add_acc(success, mload(0x80), mload(0xa0))
                    mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                    mstore(PAIRING_LHS_Y_MPTR, mload(0x20))
                    mstore(PAIRING_RHS_X_MPTR, calldataload(0x16a4))
                    mstore(PAIRING_RHS_Y_MPTR, calldataload(0x16c4))
                }
            }

            // Random linear combine with accumulator
            if mload(HAS_ACCUMULATOR_MPTR) {
                mstore(0x00, mload(ACC_LHS_X_MPTR))
                mstore(0x20, mload(ACC_LHS_Y_MPTR))
                mstore(0x40, mload(ACC_RHS_X_MPTR))
                mstore(0x60, mload(ACC_RHS_Y_MPTR))
                mstore(0x80, mload(PAIRING_LHS_X_MPTR))
                mstore(0xa0, mload(PAIRING_LHS_Y_MPTR))
                mstore(0xc0, mload(PAIRING_RHS_X_MPTR))
                mstore(0xe0, mload(PAIRING_RHS_Y_MPTR))
                let challenge := mod(keccak256(0x00, 0x100), r)

                // [pairing_lhs] += challenge * [acc_lhs]
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_LHS_X_MPTR), mload(PAIRING_LHS_Y_MPTR))
                mstore(PAIRING_LHS_X_MPTR, mload(0x00))
                mstore(PAIRING_LHS_Y_MPTR, mload(0x20))

                // [pairing_rhs] += challenge * [acc_rhs]
                mstore(0x00, mload(ACC_RHS_X_MPTR))
                mstore(0x20, mload(ACC_RHS_Y_MPTR))
                success := ec_mul_acc(success, challenge)
                success := ec_add_acc(success, mload(PAIRING_RHS_X_MPTR), mload(PAIRING_RHS_Y_MPTR))
                mstore(PAIRING_RHS_X_MPTR, mload(0x00))
                mstore(PAIRING_RHS_Y_MPTR, mload(0x20))
            }

            // Perform pairing
            success := ec_pairing(
                success,
                mload(PAIRING_LHS_X_MPTR),
                mload(PAIRING_LHS_Y_MPTR),
                mload(PAIRING_RHS_X_MPTR),
                mload(PAIRING_RHS_Y_MPTR)
            )

            // Revert if anything fails
            if iszero(success) {
                revert(0x00, 0x00)
            }

            // Return 1 as result if everything succeeds
            mstore(0x00, 1)
            return(0x00, 0x20)
        }
    }
}