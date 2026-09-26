| image | module | tests | result | s (budget) | log (16) |
| --- | --- | --- | --- | --- | --- |
| prod | test_checkpoint | 7 | OK | 30.6  | 396dffd8ab59f994 |
| prod | test_fn_verify | 33 | OK (skipped=3) | 14.6  | 8b5a491fec830c27 |
| prod | test_fn_web_native | 5 | OK | 11.9  | bee27b8c0028b5e4 |
| prod | test_native_admin | 9 | OK | 8.6  | 7ff75f41f0075118 |
| prod | test_native_auth_admin_fidelity | 3 | FAILED failures=2 | 3.2  | dbb433d0e2260d2e |
| prod | test_native_auth | 5 | OK | 8.9  | 75f9fad758c2a6bf |
| prod | test_native_block_fault_ownership | 6 | OK | 0.2  | aa219bbbe3fb75e2 |
| prod | test_native_bounds_blob | 1 | OK | 1.6  | 3e3bcfa6f91ec4c3 |
| prod | test_native_bounds_join | 2 | FAILED failures=2 | 10.9  | 6ede96cdf8d19686 |
| prod | test_native_checkpoint | 26 | FAILED failures=1 | 82.8 over | 8296c9774956c2c3 |
| prod | test_native_compaction_crash_map | 4 | OK | 0.1  | bf9ac2a62a86ce6c |
| prod | test_native_consumer_e2 | 4 | OK (skipped=1) | 11.2  | 16daf489e7483882 |
| prod | test_native_consumer_exchange | 8 | OK | 36.8  | b1ff35af2a5d87e4 |
| prod | test_native_consumer_inspect | 4 | OK | 0.7  | c0db5786f1821d75 |
| prod | test_native_consumer_project_bounds | 2 | FAILED failures=1 | 0.4  | 46da0b6722595b71 |
| prod | test_native_control_authority | 1 | OK | 2.8  | 0b5195e78db7dceb |
| prod | test_native_control_filing | 5 | OK | 20.2  | 90e1fa33e74fc9a9 |
| prod | test_native_control | 16 | FAILED failures=1 | 34.0  | f554cd3a64c384c4 |
| prod | test_native_crash_correspondence | 8 | OK | 0.1  | 3d2a48fded49f00e |
| prod | test_native_crash_model | 7 | OK | 55.4 over | 76560182a30426b1 |
| prod | test_native_cut_map | 3 | OK | 0.1  | 0de0a64749d6bac2 |
| prod | test_native_frozen_relocation | 2 | OK (skipped=2) | 0.1  | c91673844446f600 |
| prod | test_native_history_marker | 6 | OK | 5.7  | 3810919fd29db1c5 |
| prod | test_native_history_required | 6 | OK | 56.1 over | 001b40817dbe200f |
| prod | test_native_hybrid_author | 11 | FAILED failures=1 | 36.5  | 73b1d91c7a6ea71f |
| prod | test_native_initializer_fidelity | 11 | OK | 1.8  | d39aee9cd13c2063 |
| prod | test_native_key_statements | 5 | FAILED failures=2 | 11.6  | f3ef8fed1b13ee3d |
| prod | test_native_live_reconfiguration | 11 | FAILED failures=3 | 5.2  | 970e9bc245701688 |
| prod | test_native_newnews_migration | 1 | OK (skipped=1) | 0.1  | d35b59b3f3493399 |
| prod | test_native_nntp_post_probe | 13 | OK | 0.2  | 072b71e360cefdae |
| prod | test_native_operator_campaign | 5 | OK | 0.1  | a244a482d3d1449e |
| prod | test_native_operator_cli | 6 | OK | 7.0  | 9fa27bcc02260796 |
| prod | test_native_operator_verbs | 22 | OK | 9.2  | c8d2daaab9ea1261 |
| prod | test_native_operator_verdicts | 6 | OK | 14.1  | ed3ba3cc138064e8 |
| prod | test_native_owner | 18 | FAILED failures=3 | 6.4  | e7dfcd4c49f9815f |
| prod | test_native_peer_invite | 4 | FAILED failures=2 | 6.6  | 9ff157d86f023cab |
| prod | test_native_peer_pull | 13 | FAILED failures=4, skipped=1 (skipped=1) | 86.6 over | 1a310a30439e0c4c |
| prod | test_native_peering_matrix_slice | 1 | OK | 0.7  | 5799eaf1c33c616f |
| prod | test_native_peering | 5 | OK | 15.7  | b2458c1200864f77 |
| prod | test_native_profile_namespace | 1 | OK | 3.2  | 98b17ff983803b1a |
| prod | test_native_profile_upgrade | 11 | OK | 32.3  | c38538da8bc8a6d0 |
| prod | test_native_profile | 3 | OK | 3.0  | c51070e78f27dad7 |
| prod | test_native_program_check | 14 | OK | 0.8  | db5ac8a308dc7e39 |
| prod | test_native_protected_peering | 5 | OK | 35.6  | a3496749a416e671 |
| prod | test_native_raw_scripts | 9 | OK | 1.3  | a3ed51e2b4e7de7a |
| prod | test_native_reader_index | 5 | OK | 15.7  | 2e72a421dde667ae |
| prod | test_native_recovery | 13 | OK | 7.0  | c6764beab97e6dea |
| prod | test_native_served_cost | 3 | OK | 0.2  | 6612f37c3191c287 |
| prod | test_native_served_crash_model | ? | terminated; whole: OK (7ef96f7facc3e515) | 180.0 over | 86cc897bab8f297d |
| prod | test_native_served_differential | 7 | OK | 1.2  | 961870df3ac1a7c8 |
| prod | test_native_shared_owner_bench | 2 | OK | 0.2  | ba3ac0f6becbc2a6 |
| prod | test_native_source_corpus | 3 | FAILED failures=1 | 14.9  | d4b06b857d7740f7 |
| prod | test_native_stamp_migration | 1 | OK (skipped=1) | 0.1  | 08e4e8de76f33472 |
| prod | test_native_starttls | 2 | OK | 1.6  | 2c92767c44beade5 |
| prod | test_native_state_checkpoint | 6 | FAILED failures=1 | 107.4 over | 42ff0f7205693251 |
| prod | test_native_storage_codec | 11 | OK | 9.4  | f2abb3c7b37e3d0b |
| prod | test_native_tls_transport | 2 | OK | 3.8  | 18be0705f9869ec4 |
| prod | test_native_topic_local | 4 | OK (skipped=2) | 6.2  | c04da01c0a9519a6 |
| prod | test_native_topic_metadata | 2 | OK | 1.4  | 39e5d6c96c7ba5eb |
| prod | test_native_two_host_protected_gate | 5 | OK | 0.2  | bd9bf3375d9ee2bb |
| prod | test_native_v0_matrix | 67 | FAILED failures=1 | 0.9  | c4aad2edf54beee2 |
| prod | test_native_visibility_join | 3 | FAILED failures=3 | 4.3  | 4932196fe5d6e4b4 |
| prod | test_native_capacity_vector | 1 | OK | 95.7 over | 5a07c03a01dc31e7 |
| prod | test_native_consumer_exchange_two_nodes | 2 | OK | 20.0  | aa52a10f3e04c0a9 |
| prod | test_native_consumer_profile | 1 | OK | 25.8 over | 547f1491d09164a8 |
| prod | test_native_control_across_peers | 4 | OK | 29.7  | 95973271ceeb5b77 |
| prod | test_native_friends_accounts | 1 | OK | 2.0  | b0c445d4ed9dbf0e |
| prod | test_native_friends_feed | 2 | OK | 4.2  | af5a0d59f277e466 |
| prod | test_native_implicit_tls | 3 | OK | 3.1  | 088cf2a96e5ae04f |
| prod | test_native_outcome_algebra | 9 | OK | 20.2  | 51e895ba611e5d02 |
| prod | test_native_pack_chain | ? | terminated; whole: stopped (fb245698b689bbe4) | 180.0 over | d22485f51e60fc69 |
| prod | test_native_pre_c1_open | 3 | OK | 1.5  | ea10ffb722e4ffca |
| prod | test_native_public_exposure | 1 | OK | 53.2 over | 2f0649a3534f13c5 |
| prod | test_native_rollback_history | 5 | OK | 3.0  | 3c9ff8682d19637e |
| prod | test_throughput_gate | 8 | OK | 0.4  | 1495245946f11b3a |
| dev | test_checkpoint | 7 | OK | 24.7  | a3e25fcab544614d |
| dev | test_fn_verify | 33 | OK (skipped=3) | 17.4  | ec1cdeeb1fd0f5ba |
| dev | test_fn_web_native | 5 | OK | 11.5  | 980a48a0941ef3a0 |
| dev | test_native_admin | 9 | OK (skipped=9) | 6.1  | d5abc0378f5489ea |
| dev | test_native_auth_admin_fidelity | 3 | FAILED failures=2 | 4.9  | e0069f1f8b2c868e |
| dev | test_native_auth | 5 | OK | 8.2  | 193f1698427410c2 |
| dev | test_native_block_fault_ownership | 6 | OK | 0.3  | cbee69a40b0d1551 |
| dev | test_native_bounds_blob | 1 | OK | 1.6  | 7a81b8c79c425ba6 |
| dev | test_native_bounds_join | 2 | FAILED failures=2 | 10.2  | 19949604ac4e7442 |
| dev | test_native_checkpoint | 26 | FAILED failures=1 | 76.1 over | 6c55cea7f758430c |
| dev | test_native_compaction_crash_map | 4 | OK | 0.2  | fba8e02fc05337d8 |
| dev | test_native_consumer_e2 | 4 | OK (skipped=1) | 8.8  | 5e10ad01624504c3 |
| dev | test_native_consumer_exchange | 8 | OK | 25.6  | edca0a0ad63d2bd3 |
| dev | test_native_consumer_inspect | 4 | OK | 0.6  | 95d58363566c0184 |
| dev | test_native_consumer_project_bounds | 2 | FAILED failures=1 | 0.3  | d80720bfffce4e57 |
| dev | test_native_control_authority | 1 | OK | 2.6  | a057fb125faf948c |
| dev | test_native_control_filing | 5 | OK | 15.7  | ea4a503f3ad9982f |
| dev | test_native_control | ? | terminated; whole: stopped (e53d35210e2db2fb) | 180.0 over | e42c70b055f53801 |
| dev | test_native_crash_correspondence | 8 | OK | 0.2  | e7c062a742197d09 |
| dev | test_native_crash_model | 7 | OK | 55.0 over | 8ba86c07c8b013a6 |
| dev | test_native_cut_map | 3 | OK | 0.1  | 3bb64d7c32304927 |
| dev | test_native_frozen_relocation | 2 | OK (skipped=2) | 0.1  | c91673844446f600 |
| dev | test_native_history_marker | 6 | OK | 5.7  | 5c5a3846e27b9008 |
| dev | test_native_history_required | 6 | OK | 53.6 over | 8b99f51c4465f87e |
| dev | test_native_hybrid_author | 11 | FAILED failures=1 | 34.7  | e6f2ddd219e6d441 |
| dev | test_native_initializer_fidelity | 11 | OK | 1.6  | 9a10fbe2f4420218 |
| dev | test_native_key_statements | 5 | OK | 17.4  | d61391aecbc24ad6 |
| dev | test_native_live_reconfiguration | 11 | FAILED failures=3 | 5.1  | b27e8f83ce778df3 |
| dev | test_native_newnews_migration | 1 | OK (skipped=1) | 0.1  | d35b59b3f3493399 |
| dev | test_native_nntp_post_probe | 13 | OK | 0.6  | d0fa409a6002627f |
| dev | test_native_operator_campaign | 5 | OK | 0.1  | a244a482d3d1449e |
| dev | test_native_operator_cli | 6 | OK | 6.9  | c240b4e3ebc4c847 |
| dev | test_native_operator_verbs | 22 | FAILED errors=1 | 127.8 over | 866e4acf65fa0767 |
| dev | test_native_operator_verdicts | 6 | OK | 14.3  | 44d1e7185ed48a8e |
| dev | test_native_owner | 18 | FAILED failures=2 | 8.2  | 3dacc7bb5084f2b5 |
| dev | test_native_peer_invite | 4 | OK | 12.8  | d288a516b0521d98 |
| dev | test_native_peer_pull | 13 | OK (skipped=1) | 115.8 over | 7f47621aee3c5b61 |
| dev | test_native_peering_matrix_slice | 1 | OK | 0.4  | 10c35969c741e67a |
| dev | test_native_peering | 5 | OK (skipped=5) | 0.4  | dc7e5ef664e6f973 |
| dev | test_native_profile_namespace | 1 | OK | 2.5  | 6301910f9b8c7b2d |
| dev | test_native_profile_upgrade | 11 | OK | 27.3  | cebff05b4da7dd63 |
| dev | test_native_profile | 3 | OK | 2.7  | 6f07eb90fff04088 |
| dev | test_native_program_check | 14 | OK | 0.7  | 022e47d94c8ba110 |
| dev | test_native_protected_peering | 5 | OK (skipped=5) | 0.5  | 7800c217fa90b4c7 |
| dev | test_native_raw_scripts | 9 | OK | 0.9  | fe242a4cb7b833c9 |
| dev | test_native_reader_index | 5 | OK | 12.9  | 58b48a99d44ffaa1 |
| dev | test_native_recovery | 13 | OK | 2.1  | 370bfafb6546688c |
| dev | test_native_served_cost | 3 | OK | 0.1  | 0421516e0fc8b8ac |
| dev | test_native_served_crash_model | ? | terminated; whole: OK (2519c54a52a6e121) | 180.0 over | 86cc897bab8f297d |
| dev | test_native_served_differential | 7 | OK | 1.4  | 4f3fd2d2d4e904c7 |
| dev | test_native_shared_owner_bench | 2 | OK | 0.3  | ba3ac0f6becbc2a6 |
| dev | test_native_source_corpus | 3 | FAILED failures=1 | 14.7  | f77aeed642f29c3a |
| dev | test_native_stamp_migration | 1 | OK (skipped=1) | 0.1  | 08e4e8de76f33472 |
| dev | test_native_starttls | 2 | OK | 1.7  | 5449945320870774 |
| dev | test_native_state_checkpoint | 6 | FAILED failures=1 | 108.7 over | a8d51c39814f8879 |
| dev | test_native_storage_codec | 11 | OK | 7.3  | 2cc99d8ce1b72122 |
| dev | test_native_tls_transport | 2 | OK | 1.3  | 343c0addbbaac4fa |
| dev | test_native_topic_local | 4 | OK (skipped=2) | 6.2  | a42e11a93eea5c2f |
| dev | test_native_topic_metadata | 2 | OK | 1.3  | a077ec4bc4f56ce3 |
| dev | test_native_two_host_protected_gate | 5 | OK | 0.2  | eb9b3a8bf36988bf |
| dev | test_native_v0_matrix | 67 | FAILED failures=1 | 0.6  | 9cb99b764f841bd9 |
| dev | test_native_visibility_join | 3 | OK | 9.6  | 0da95dc8be1c741d |
| dev | test_native_capacity_vector | 1 | OK | 96.6 over | f960e5c38ab84e67 |
| dev | test_native_consumer_exchange_two_nodes | 2 | OK | 24.9  | e62fe22b6fbcb75d |
| dev | test_native_consumer_profile | 1 | OK | 38.3 over | f340197d7c164a88 |
| dev | test_native_control_across_peers | 4 | OK | 41.8 over | c8c5d60e04a6305b |
| dev | test_native_friends_accounts | 1 | OK | 7.0  | 7474d30c53b3b596 |
| dev | test_native_friends_feed | 2 | OK | 4.9  | a4b60ee632fcf622 |
| dev | test_native_implicit_tls | 3 | OK | 3.7  | a538e942ac2eef0f |
| dev | test_native_outcome_algebra | 9 | FAILED errors=1 | 127.7 over | b56f46c770312cc1 |
| dev | test_native_pack_chain | ? | terminated; whole: stopped (06b6790f2cc7e736) | 180.0 over | d22485f51e60fc69 |
| dev | test_native_pre_c1_open | 3 | OK | 1.4  | 794bf3dbefe458b8 |
| dev | test_native_public_exposure | 1 | OK | 54.3 over | 8861528098a91d53 |
| dev | test_native_rollback_history | 5 | OK | 3.5  | 4f36a53914534954 |
| dev | test_throughput_gate | 8 | OK | 0.5  | a6879ee690726ef1 |
| dtn | test_bp_service_native | 17 | FAILED failures=7 | 6.9  | 79451241cd346dde |
| dtn | test_bp_contact_native | 2 | OK | 0.9  | eab5bb7636c84d98 |
| dtn | test_bp_contact_relay_native | 1 | OK | 2.4  | 42ad54bd86638d21 |
| dtn | test_bp_app_native | 7 | OK | 36.3 over | 04c49f73e9e1d190 |
| dtn | test_bp_node_native | 27 | FAILED failures=27 | 16.2  | dc655e062cd3f546 |
| dtn | test_bp_receive_integrity_native | 4 | FAILED failures=2 | 0.7  | 94e5d0493d560c1a |
| dtn | test_bp_fragment_node_native | ? | terminated; whole: FAILED (errors=1) (8d6f47ed4549ecb3) | 180.0 over | 73a8516c297490ce |
| dtn | test_bp_obligation_native | 5 | FAILED failures=1 | 4.4  | 17ecd2975d895e6f |
| dtn | test_native_source_corpus_bp | 1 | OK | 129.9 over | 5fa80e87af665715 |
| dtn | test_native_bp_app_clock | 1 | OK | 0.2  | 6dd10df1ed548c31 |
| dtn | test_native_bp_channel_admission | 1 | OK | 0.1  | eb79a853c48e30c7 |
| dtn | test_native_bp_node_admission_lock | 1 | OK | 0.1  | 702004b80480350c |
| dtn | test_native_bp_transit_identity | 1 | OK | 0.1  | cbe71fdc4ced899f |
| dtn | test_native_app_journal | 10 | OK | 4.8  | c39d16dd8505477a |
| dtn | test_native_image_profiles | 12 | OK | 1.8  | 7ee5d2a783ce0096 |
| dtndev | test_bp_service_native | 17 | OK | 21.4  | 55e8d96cfb8d0178 |
| dtndev | test_bp_contact_native | 2 | OK | 1.0  | f905620a96f1999e |
| dtndev | test_bp_contact_relay_native | 1 | OK | 2.9  | 3ac278f2b490eb11 |
| dtndev | test_bp_app_native | 7 | OK | 25.0  | d1cc1a085bb24c29 |
| dtndev | test_bp_node_native | 27 | OK | 142.5 over | 118d6f3b652a5c24 |
| dtndev | test_bp_receive_integrity_native | 4 | OK | 1.1  | a89a951a31213805 |
| dtndev | test_bp_fragment_node_native | ? | terminated; whole: FAILED (errors=1) (d70cd02f6c16ef69) | 180.0 over | 6e48a4838ea4da2a |
| dtndev | test_bp_obligation_native | 5 | FAILED failures=1 | 3.6  | 9f50ae10e9046272 |
| dtndev | test_native_source_corpus_bp | 1 | OK | 147.4 over | dee9717c6c94084f |
| dtndev | test_native_bp_app_clock | 1 | OK | 0.3  | b70c35ec74c8c01c |
| dtndev | test_native_bp_channel_admission | 1 | OK | 0.3  | 4394614e82231d07 |
| dtndev | test_native_bp_node_admission_lock | 1 | OK | 0.2  | b5fbd6fbb6d25dc5 |
| dtndev | test_native_bp_transit_identity | 1 | OK | 0.2  | c24f0fed26de2a3b |
| dtndev | test_native_app_journal | 10 | OK | 5.5  | 19d8636ee52ab9ec |
| dtndev | test_native_image_profiles | 12 | OK | 2.3  | ae875b0368008e33 |
