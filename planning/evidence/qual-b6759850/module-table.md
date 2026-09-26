| image | module | tests | result | s (budget) | log (16) |
| --- | --- | --- | --- | --- | --- |
| prod | test_checkpoint | 7 | OK | 27.2  | a18e8aab8fcfd8aa |
| prod | test_fn_verify | 31 | OK | 11.9  | c71ff2ed019f835b |
| prod | test_fn_web_native | 4 | FAILED failures=1 | 5.8  | ef381379844448c3 |
| prod | test_native_admin | 9 | OK | 7.7  | 79ccdb4bdb57568d |
| prod | test_native_auth_admin_fidelity | 3 | OK | 5.9  | b52d176272a92a01 |
| prod | test_native_auth | 4 | OK | 6.7  | 310b4b3e20c25625 |
| prod | test_native_block_fault_ownership | 6 | OK | 2.0  | 35255a6e6503532f |
| prod | test_native_bounds_blob | 1 | OK | 1.5  | 3b39b85f01affbec |
| prod | test_native_bounds_join | 2 | OK | 20.4  | 8cf356c46e94eb40 |
| prod | test_native_checkpoint | 26 | OK | 75.9 over | 7e201842c075dc73 |
| prod | test_native_compaction_crash_map | 4 | OK | 0.1  | aa1093b5a9dcdebe |
| prod | test_native_consumer_e2 | 4 | OK | 8.7  | 3fa97e6e6e9a1470 |
| prod | test_native_consumer_exchange | 3 | OK | 10.2  | cc1e312aa50b8105 |
| prod | test_native_consumer_inspect | 4 | OK | 0.5  | 39a5e2c9c4c5800a |
| prod | test_native_consumer_project_bounds | 2 | FAILED failures=1 | 0.3  | 4054f8fd618494bb |
| prod | test_native_control_authority | 1 | OK | 2.5  | 35f30e18fb3772b9 |
| prod | test_native_control_filing | 5 | OK | 15.6  | 7eaba7d33e298e2b |
| prod | test_native_control | 14 | FAILED failures=1 | 27.1  | c937afc0183dc214 |
| prod | test_native_crash_correspondence | 8 | OK | 0.1  | 5b0e77b75b56ed0e |
| prod | test_native_crash_model | 7 | OK | 47.6 over | a895285e4810d249 |
| prod | test_native_cut_map | 3 | OK | 0.1  | 4b2874fa5a75f7c9 |
| prod | test_native_frozen_relocation | 2 | OK | 0.1  | c91673844446f600 |
| prod | test_native_history_marker | 6 | OK | 4.9  | 8c6ac74ef090b63b |
| prod | test_native_history_required | 6 | OK | 49.7 over | e55f0638eddded45 |
| prod | test_native_hybrid_author | 10 | FAILED failures=1 | 30.5  | 7fbf27a87a6a9a0c |
| prod | test_native_initializer_fidelity | 11 | OK | 1.6  | a24fbd09059cfed5 |
| prod | test_native_key_statements | 3 | FAILED failures=1 | 7.4  | c4f1890e353825fb |
| prod | test_native_live_reconfiguration | 11 | FAILED failures=1 | 3.9  | 5782b2b68140b941 |
| prod | test_native_newnews_migration | 1 | OK | 0.1  | d35b59b3f3493399 |
| prod | test_native_nntp_post_probe | 13 | OK | 0.2  | a3f18adaaa795364 |
| prod | test_native_operator_campaign | 5 | OK | 0.1  | a244a482d3d1449e |
| prod | test_native_operator_cli | 6 | OK | 6.8  | a74ec6acdd6c8df9 |
| prod | test_native_operator_verbs | 22 | FAILED failures=1 | 8.6  | 88e5fbcfaf504f6a |
| prod | test_native_operator_verdicts | 6 | OK | 11.7  | 448282fadac2c4c5 |
| prod | test_native_owner | 18 | FAILED failures=1 | 7.3  | eab9a703b4e34cc7 |
| prod | test_native_peer_invite | 3 | FAILED failures=1 | 4.7  | 2fa0a4b10847c462 |
| prod | test_native_peer_pull | 8 | FAILED failures=2 | 68.1 over | b06b2683ccc6b77c |
| prod | test_native_peering_matrix_slice | 1 | OK | 0.2  | 72c066bdf0fb0050 |
| prod | test_native_peering | 5 | OK | 9.9  | 34909857bcbcb5e9 |
| prod | test_native_profile_namespace | 1 | OK | 2.0  | 6bedd5e60c2ed4f8 |
| prod | test_native_profile_upgrade | 11 | OK | 22.4  | dedcd12c1424b072 |
| prod | test_native_profile | 3 | OK | 2.6  | eddac1bca68fcb76 |
| prod | test_native_program_check | 9 | OK | 0.5  | bae73a6926c5a1da |
| prod | test_native_protected_peering | 5 | OK | 27.2  | 2f86ec4ce60024e9 |
| prod | test_native_raw_scripts | 9 | OK | 0.5  | 6a7a87f34be1f713 |
| prod | test_native_reader_index | 5 | OK | 12.8  | 23131fde8096fc5f |
| prod | test_native_recovery | 13 | OK | 2.1  | b3d4831033d184da |
| prod | test_native_served_cost | 3 | OK | 0.1  | 0421516e0fc8b8ac |
| prod | test_native_served_crash_model | ? | terminated; whole: stopped (801f42b78ea798f5) | 180.1 over | 44bb34956762bfab |
| prod | test_native_served_differential | 7 | OK | 1.0  | 3dd2007828c26453 |
| prod | test_native_shared_owner_bench | 2 | OK | 0.1  | ba3ac0f6becbc2a6 |
| prod | test_native_source_corpus | 3 | OK | 14.6  | 9ad96b7b2edf2d44 |
| prod | test_native_stamp_migration | 1 | OK | 0.1  | 08e4e8de76f33472 |
| prod | test_native_starttls | 2 | OK | 1.6  | ceb198133d280221 |
| prod | test_native_state_checkpoint | 5 | OK | 98.7 over | 545a737887cec29b |
| prod | test_native_storage_codec | 11 | OK | 5.9  | 62a438616aa21ad0 |
| prod | test_native_tls_transport | 2 | OK | 1.0  | 62cb94987b5e2056 |
| prod | test_native_topic_local | 4 | OK | 4.8  | b7912d66d5e37a74 |
| prod | test_native_topic_metadata | 2 | OK | 1.1  | 8acd9e114f03f77d |
| prod | test_native_two_host_protected_gate | 5 | OK | 0.1  | 1134473374fbe0a3 |
| prod | test_native_v0_matrix | 67 | OK | 0.4  | 50396a5b4efb97f3 |
| prod | test_native_visibility_join | 2 | FAILED failures=2 | 1.2  | 9a0479b2aaf47984 |
| dev | test_checkpoint | 7 | FAILED failures=2 | 13.5  | 2b6c5706454a5969 |
| dev | test_fn_verify | 31 | OK | 17.2  | ef4067dd4509ad03 |
| dev | test_fn_web_native | 4 | FAILED failures=1 | 5.8  | d3a7144da2543b8b |
| dev | test_native_admin | 9 | OK | 0.5  | d5abc0378f5489ea |
| dev | test_native_auth_admin_fidelity | 3 | OK | 5.5  | 8237c34ec45f44dd |
| dev | test_native_auth | 4 | OK | 6.5  | 161c7f46b6e49c6e |
| dev | test_native_block_fault_ownership | 6 | OK | 0.2  | 47b45971c675908a |
| dev | test_native_bounds_blob | 1 | OK | 1.5  | 3b39b85f01affbec |
| dev | test_native_bounds_join | 2 | OK | 22.1  | b1cbfe36f2df26d6 |
| dev | test_native_checkpoint | 26 | OK | 77.1 over | c0f98c6149585188 |
| dev | test_native_compaction_crash_map | 4 | OK | 0.1  | aa1093b5a9dcdebe |
| dev | test_native_consumer_e2 | 4 | OK | 8.9  | fde7f0ef372b94c4 |
| dev | test_native_consumer_exchange | 3 | OK | 10.2  | 8f1ad6bab4880740 |
| dev | test_native_consumer_inspect | 4 | OK | 0.5  | 0ed6fe79fa3dcb1a |
| dev | test_native_consumer_project_bounds | 2 | FAILED failures=1 | 0.3  | 00e772e873c1b481 |
| dev | test_native_control_authority | 1 | OK | 2.6  | f317c67913b84eef |
| dev | test_native_control_filing | 5 | OK | 15.7  | b3442a1c6a69ce2c |
| dev | test_native_control | ? | terminated; whole: stopped (23da5b0abb6b848b) | 180.0 over | bdcf580bf3c62fc6 |
| dev | test_native_crash_correspondence | 8 | OK | 0.2  | f74f2aada89cec6a |
| dev | test_native_crash_model | 7 | OK | 50.4 over | 956817c9c73047a6 |
| dev | test_native_cut_map | 3 | OK | 0.1  | 2b0d105a78b7f3f3 |
| dev | test_native_frozen_relocation | 2 | OK | 0.1  | c91673844446f600 |
| dev | test_native_history_marker | 6 | OK | 5.4  | 90e8aa8f5049c6b2 |
| dev | test_native_history_required | 6 | OK | 54.3 over | 8f3b351e8e831297 |
| dev | test_native_hybrid_author | 10 | FAILED failures=1 | 34.4  | 47c772887e471ac3 |
| dev | test_native_initializer_fidelity | 11 | OK | 1.8  | c9d20a37edea4cbf |
| dev | test_native_key_statements | 3 | OK | 10.8  | 09bbafae77fba69f |
| dev | test_native_live_reconfiguration | 11 | FAILED failures=1 | 4.1  | 72b0beefe943daae |
| dev | test_native_newnews_migration | 1 | OK | 0.1  | d35b59b3f3493399 |
| dev | test_native_nntp_post_probe | 13 | OK | 0.3  | 337d25405bc0adfe |
| dev | test_native_operator_campaign | 5 | OK | 0.1  | a244a482d3d1449e |
| dev | test_native_operator_cli | 6 | OK | 7.0  | d3e01697a3aeb2ed |
| dev | test_native_operator_verbs | 22 | FAILED failures=1, errors=1 | 127.6 over | 0077a3bcf3143d32 |
| dev | test_native_operator_verdicts | 6 | OK | 13.0  | 5eba5960433d8414 |
| dev | test_native_owner | 18 | FAILED failures=1 | 7.7  | e94e57dae4804e13 |
| dev | test_native_peer_invite | 3 | OK | 8.1  | f86169f57d0f0992 |
| dev | test_native_peer_pull | 8 | OK | 95.2 over | bbc16249adefbc45 |
| dev | test_native_peering_matrix_slice | 1 | OK | 0.2  | 62039257ad9aef0e |
| dev | test_native_peering | 5 | OK | 0.4  | dc7e5ef664e6f973 |
| dev | test_native_profile_namespace | 1 | OK | 2.2  | 093eb8f22d8a49cf |
| dev | test_native_profile_upgrade | 11 | OK | 24.2  | c991178c4f4d4c66 |
| dev | test_native_profile | 3 | OK | 2.7  | f11cf6a19f06b9ce |
| dev | test_native_program_check | 9 | OK | 0.5  | 19b299e8376b4fb0 |
| dev | test_native_protected_peering | 5 | OK | 0.4  | 7800c217fa90b4c7 |
| dev | test_native_raw_scripts | 9 | OK | 0.5  | 8e8a64d840a8daa5 |
| dev | test_native_reader_index | 5 | OK | 12.8  | a57f83a09342d4de |
| dev | test_native_recovery | 13 | OK | 2.0  | 6b2ded59e9d82325 |
| dev | test_native_served_cost | 3 | OK | 0.1  | 0421516e0fc8b8ac |
| dev | test_native_served_crash_model | ? | terminated; whole: FAILED (errors=26) (e39e2fc574ae4da3) | 180.0 over | 6a83e7f83be13ac5 |
| dev | test_native_served_differential | 7 | OK | 1.1  | 4ac70421458bd658 |
| dev | test_native_shared_owner_bench | 2 | OK | 0.1  | ba3ac0f6becbc2a6 |
| dev | test_native_source_corpus | 3 | OK | 14.2  | 1aed7ef7166088fa |
| dev | test_native_stamp_migration | 1 | OK | 0.1  | 08e4e8de76f33472 |
| dev | test_native_starttls | 2 | OK | 1.6  | af340b233d7a967e |
| dev | test_native_state_checkpoint | 5 | OK | 93.6 over | b14c2f60bb2b02aa |
| dev | test_native_storage_codec | 11 | OK | 5.7  | 19bde024f4891c6e |
| dev | test_native_tls_transport | 2 | OK | 1.0  | 5281ece0e651ccab |
| dev | test_native_topic_local | 4 | OK | 4.7  | eab2b49f43e16dbb |
| dev | test_native_topic_metadata | 2 | OK | 0.9  | 2c3e6e7ba13f32b7 |
| dev | test_native_two_host_protected_gate | 5 | OK | 0.1  | e587785df95df363 |
| dev | test_native_v0_matrix | 67 | OK | 0.4  | 65fb3909b1b8e8fb |
| dev | test_native_visibility_join | 2 | OK | 5.0  | f2a2a75f6188f095 |
| dtn | test_bp_service_native | 17 | FAILED failures=7 | 6.3  | 245b77c0ad0156d8 |
| dtn | test_bp_contact_native | 2 | OK | 0.7  | 6a01873307b39b41 |
| dtn | test_bp_contact_relay_native | 1 | OK | 2.3  | c0a8e4609ef2962b |
| dtn | test_bp_app_native | 5 | OK | 24.9 over | 14d9c606b7504bff |
| dtn | test_bp_node_native | 27 | FAILED failures=27 | 11.1  | b3b584393b341381 |
| dtn | test_bp_receive_integrity_native | 4 | FAILED failures=2 | 0.6  | ef0f24c46c2957e4 |
| dtn | test_bp_fragment_node_native | ? | terminated; whole: stopped (bc2edff1622166b7) | 180.0 over | 83eafe1f9be8c84e |
| dtn | test_bp_obligation_native | 5 | FAILED failures=1 | 3.0  | 3678ffa04e188f07 |
| dtn | test_native_source_corpus_bp | 1 | OK | 121.1 over | d087729c0ebb5f9f |
| dtn | test_native_bp_app_clock | 1 | OK | 0.2  | 8ab534304d7fad5e |
| dtn | test_native_bp_channel_admission | 1 | FAILED failures=1 | 0.1  | ac96776489c5bf9e |
| dtn | test_native_bp_node_admission_lock | 1 | FAILED failures=1 | 0.1  | 7718bf45a54b9ece |
| dtn | test_native_bp_transit_identity | 1 | OK | 0.1  | cbe71fdc4ced899f |
| dtn | test_native_app_journal | 10 | OK | 4.3  | 57bdf07ea3fd6c40 |
| dtn | test_native_image_profiles | 12 | OK | 1.3  | 0298240e34aeaaab |
| dtndev | test_bp_service_native | 17 | OK | 20.1  | 56ff865eee9c9a4f |
| dtndev | test_bp_contact_native | 2 | OK | 0.7  | fb73b5d4d53bc189 |
| dtndev | test_bp_contact_relay_native | 1 | OK | 2.3  | c3dde3657c0ee606 |
| dtndev | test_bp_app_native | 5 | OK | 8.4  | 730dafe2e9d96a5c |
| dtndev | test_bp_node_native | 27 | OK | 117.0 over | 8407db4e55fb2f91 |
| dtndev | test_bp_receive_integrity_native | 4 | OK | 1.0  | e69b95e5362eb79f |
| dtndev | test_bp_fragment_node_native | ? | terminated; whole: stopped (407156f0f86b8d5c) | 180.0 over | 0a3cbd60e20112ea |
| dtndev | test_bp_obligation_native | 5 | FAILED failures=1 | 3.0  | c67f927661d7c68c |
| dtndev | test_native_source_corpus_bp | 1 | OK | 127.0 over | 5cb6178aea371042 |
| dtndev | test_native_bp_app_clock | 1 | OK | 0.6  | b567b8f8be918f9f |
| dtndev | test_native_bp_channel_admission | 1 | FAILED failures=1 | 0.3  | abd765409583bd5c |
| dtndev | test_native_bp_node_admission_lock | 1 | FAILED failures=1 | 0.2  | 400b79ad17c431e9 |
| dtndev | test_native_bp_transit_identity | 1 | OK | 0.2  | fcf7edb6291f93ea |
| dtndev | test_native_app_journal | 10 | OK | 5.5  | 522599efd40e03ee |
| dtndev | test_native_image_profiles | 12 | OK | 1.7  | 46d9c626e16cd690 |
