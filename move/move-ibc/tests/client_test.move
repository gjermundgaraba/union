// #[test_only]
// module IBC::ClientTest {

//     use aptos_std::string;
//     use aptos_std::any;
//     use IBC::height;
//     use IBC::ibc;
//     use IBC::LightClient;

//     const E_GENERATE_CLIENT_IDENTIFIER: u64 = 3001;
//     const E_GET_CLIENT_IMPL: u64 = 3002;
//     const E_CREATE_CLIENT: u64 = 3003;

//     #[test(alice = @IBC)]
//     public fun test_generate_client_identifier(alice: &signer) {
//         ibc::create_ibc_store(alice);

//         let client_type = string::utf8(b"test_client");

//         // Generate the first identifier
//         let identifier1 = ibc::generate_client_identifier(client_type);
//         let expected_identifier1 = string::utf8(b"test_client-0");
//         assert!(identifier1 == expected_identifier1, E_GENERATE_CLIENT_IDENTIFIER);

//         // Generate the second identifier
//         let identifier2 = ibc::generate_client_identifier(client_type);
//         let expected_identifier2 = string::utf8(b"test_client-1");
//         assert!(identifier2 == expected_identifier2, E_GENERATE_CLIENT_IDENTIFIER);
//     }

//     #[test(alice = @IBC)]
//     public fun test_create_client(alice: &signer) {
//         ibc::create_ibc_store(alice);

//         // Register the mock client type and address
//         let client_type = string::utf8(b"mock_client");

//         let expected_client_id = string::utf8(b"mock_client-0");

//         let client_state = any::pack(LightClient::new_client_state(
//             string::utf8(b"this-chain"),
//             0,
//             0,
//             0,
//             height::new(0, 0),
//             height::new(0, 1000)
//         ));

//         let consensus_state = any::pack(LightClient::new_consensus_state(
//             10000,
//             LightClient::new_merkle_root(vector<u8>[]),
//             vector<u8>[]
//         ));

//         let client_id = ibc::create_client(
//             client_type,
//             client_state,
//             consensus_state,
//         );
//         assert!(client_id == expected_client_id, E_CREATE_CLIENT);

//         // Register the mock client type and address
//         let client_type2 = string::utf8(b"another_client");

//         let expected_client_id2 = string::utf8(b"another_client-1");

//         let client_state2 = any::pack(LightClient::new_client_state(
//             string::utf8(b"that-chain"),
//             0,
//             0,
//             0,
//             height::new(0, 0),
//             height::new(0, 1000)
//         ));

//         let consensus_state2 = any::pack(LightClient::new_consensus_state(
//             10000,
//             LightClient::new_merkle_root(vector<u8>[]),
//             vector<u8>[]
//         ));

//         let client_id2 = ibc::create_client(
//             client_type2,
//             client_state2,
//             consensus_state2,
//         );
//         assert!(client_id2 == expected_client_id2, E_CREATE_CLIENT);

//     }
// }
