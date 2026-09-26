| image | module | tests | result | s (budget) | log (16) |
| --- | --- | --- | --- | --- | --- |
| prod | test_checkpoint | 7 | FAILED errors=1 | 29.4  | 72debff82dc77602 |
| prod | test_fn_verify | 33 | OK (skipped=3) | 18.1  | 3c52610e99e6dab0 |
| prod | test_fn_web_native | 5 | OK | 14.0  | d3c648eaff3a2e9a |
| prod | test_native_admin | 9 | OK | 10.0  | c21eea8065a45d1a |
| prod | test_native_auth_admin_fidelity | 3 | FAILED failures=2 | 3.7  | b1d02e3b6773c46c |
| prod | test_native_auth | 5 | OK | 10.2  | fbe9764b975f8a4f |
| prod | test_native_block_fault_ownership | 6 | OK | 0.2  | 2fb2b1739078b527 |
| prod | test_native_bounds_blob | 1 | OK | 3.0  | 64be707c5c2d8b5d |
| prod | test_native_bounds_join | 3 | OK | 50.6 over | 999bd5ff4a4d5f88 |
| prod | test_native_checkpoint | 26 | FAILED failures=1 | 95.4 over | e81da83dc84cdd88 |
| prod | test_native_compaction_crash_map | 4 | OK | 0.1  | 528a36d9abf196ea |
| prod | test_native_consumer_e2 | 4 | OK (skipped=1) | 10.7  | 0dc756d2b58a377b |
| prod | test_native_consumer_exchange | 8 | OK | 32.2  | ca9bc2238e703c2b |
| prod | test_native_consumer_inspect | 4 | OK | 0.6  | b25b700fa1a7430d |
| prod | test_native_consumer_project_bounds | 2 | FAILED failures=1 | 0.3  | 8bdbeafaedc4bbcf |
| prod | test_native_control_authority | 1 | OK | 2.7  | d268b470ed011ffa |
| prod | test_native_control_filing | 5 | OK | 18.1  | c7be9f7d22d5d9fe |
| prod | test_native_control | 18 | OK | 32.5  | 0b213db160678a57 |
| prod | test_native_crash_correspondence | 8 | OK | 0.1  | 0b97d1566ddd2cc3 |
| prod | test_native_crash_model | 7 | OK | 55.0 over | 395e2cbfca78e4a1 |
| prod | test_native_cut_map | 3 | OK | 0.1  | 8d8b0b99c499002c |
| prod | test_native_frozen_relocation | 2 | OK (skipped=2) | 0.1  | 1c244c35aa39a3fa |
| prod | test_native_history_marker | 6 | OK | 6.2  | e75320d8ee7fa2ee |
| prod | test_native_history_required | 6 | FAILED failures=1 | 57.6 over | 165777e952459835 |
| prod | test_native_hybrid_author | 11 | OK | 38.7  | f2345425bf348079 |
| prod | test_native_initializer_fidelity | 11 | OK | 2.1  | ed1fcc432b46d949 |
| prod | test_native_key_statements | 5 | FAILED failures=2 | 11.8  | 0ac19b6428d260ab |
| prod | test_native_live_reconfiguration | 11 | FAILED failures=3 | 5.1  | 14bae2d68637b1b2 |
| prod | test_native_newnews_migration | 1 | OK (skipped=1) | 0.1  | 25a83f535474c39f |
| prod | test_native_nntp_post_probe | 13 | OK | 0.2  | 86d0bbf1865d1663 |
| prod | test_native_operator_campaign | 5 | OK | 0.1  | 29d5be86e7ddf908 |
| prod | test_native_operator_cli | 6 | OK | 7.1  | cdd68f06177eb723 |
| prod | test_native_operator_verbs | 22 | FAILED failures=1 | 9.6  | 69c7f012a834e50b |
| prod | test_native_operator_verdicts | 6 | OK | 14.1  | 957863fa597c2329 |
| prod | test_native_owner | 18 | FAILED failures=2 | 6.6  | a918ea6364c92de9 |
| prod | test_native_peer_invite | 5 | FAILED failures=2 | 11.6  | 5e1216379008af16 |
| prod | test_native_peer_pull | 13 | FAILED failures=4, skipped=1 (skipped=1) | 75.1 over | 8fa56e00a38fac05 |
| prod | test_native_peering_matrix_slice | 1 | OK | 0.2  | b3e7d53786298d97 |
| prod | test_native_peering | 5 | OK | 13.0  | fbd73e419a539333 |
| prod | test_native_profile_namespace | 1 | OK | 2.6  | ac157236ccedd9cb |
| prod | test_native_profile_upgrade | 11 | FAILED failures=1 | 32.9  | 1355a8ebc6221e3a |
| prod | test_native_profile | 3 | OK | 2.8  | a6f0a8fd5493cdfb |
| prod | test_native_program_check | 14 | OK | 1.0  | b2e86f3b34ab8d7f |
| prod | test_native_protected_peering | 5 | OK | 39.5  | 436bd0989bae4100 |
| prod | test_native_raw_scripts | 9 | OK | 0.9  | bf7ae75d5ae82449 |
| prod | test_native_reader_index | 5 | OK | 15.3  | dd406c94011dece0 |
| prod | test_native_recovery | 13 | OK | 3.4  | abeceb3c8c6a76ed |
| prod | test_native_served_cost | 3 | OK | 0.1  | e9b7cb1414c23242 |
| prod | test_native_served_crash_model | ? | terminated; whole: OK (43e8e5fa5085a1a5) | 180.0 over | 86cc897bab8f297d |
| prod | test_native_served_differential | 7 | OK | 1.1  | af53d4115ac79a58 |
| prod | test_native_shared_owner_bench | 2 | OK | 0.1  | db7d6675bb587ff3 |
| prod | test_native_source_corpus | 3 | FAILED failures=1 | 13.9  | 084193bb607d2f6d |
| prod | test_native_stamp_migration | 1 | OK (skipped=1) | 0.1  | 7a4cafdaaa3e41ec |
| prod | test_native_starttls | 2 | OK | 1.8  | 2ed3324218369a7b |
| prod | test_native_state_checkpoint | 6 | FAILED failures=1 | 113.7 over | c722a59f7a93cea8 |
| prod | test_native_storage_codec | 11 | OK | 6.7  | 86be683e4c56c16e |
| prod | test_native_tls_transport | 2 | OK | 1.0  | c22294636ebc3483 |
| prod | test_native_topic_local | 4 | OK (skipped=2) | 4.8  | 542b001b0f56a0e3 |
| prod | test_native_topic_metadata | 2 | OK | 1.1  | d38ef41d6a742875 |
| prod | test_native_two_host_protected_gate | 5 | OK | 0.1  | 697f08c044a264ff |
| prod | test_native_v0_matrix | 67 | FAILED failures=1 | 0.4  | 5b477d7a2ca9d240 |
| prod | test_native_visibility_join | 3 | FAILED failures=3 | 3.2  | 6c6d182b9177b55d |
| prod | test_native_capacity_vector | 1 | OK | 82.3 over | c18fef0d40b8a2ac |
| prod | test_native_consumer_exchange_two_nodes | 2 | OK | 22.2  | 4455a9e3dd20874e |
| prod | test_native_consumer_profile | 1 | OK | 36.2 over | 58f449f486233463 |
| prod | test_native_control_across_peers | 4 | OK | 36.5  | 5516b37d9fc98bef |
| prod | test_native_friends_accounts | 1 | OK | 1.9  | 2c978c63ef7f282a |
| prod | test_native_friends_feed | 2 | OK | 4.3  | 877ae5a41d33887c |
| prod | test_native_implicit_tls | 3 | OK | 3.2  | b2443cb2bafe4915 |
| prod | test_native_outcome_algebra | 9 | OK | 7.6  | 3e1c8255602282b6 |
| prod | test_native_pack_chain | ? | terminated; whole: stopped (f839de54ee7026a0) | 180.0 over | d22485f51e60fc69 |
| prod | test_native_pre_c1_open | 3 | OK | 0.9  | 1a76979017714b18 |
| prod | test_native_public_exposure | 1 | OK | 53.9 over | f4a6436b4247766d |
| prod | test_native_rollback_history | 5 | OK | 3.0  | f2170ff856b377fe |
| prod | test_throughput_gate | 12 | OK | 0.3  | 6efb919d12b6e80b |
| prod | test_native_checkpoint_generations | 2 | OK | 1.2  | 2997ef71da226da7 |
| prod | test_native_control_evidence | 1 | OK | 2.8  | f9adf36d0ff09f75 |
| prod | test_native_control_reply_fit | 5 | OK | 7.7  | 9ee81140408edfd0 |
| prod | test_native_peer_rows_growth | ? | terminated; whole: stopped (3be1ad63d2f4591c) | 180.1 over | 65aca5b01d767392 |
| dev | test_checkpoint | 7 | FAILED errors=1 | 13.9  | 3ec68a9e8ea6d49c |
| dev | test_fn_verify | 33 | OK (skipped=3) | 11.4  | 25f0cb66b8f32945 |
| dev | test_fn_web_native | 5 | OK | 11.5  | 68a0e0aa3c97e29d |
| dev | test_native_admin | 9 | OK (skipped=9) | 0.3  | 7b5fd3b9d1092219 |
| dev | test_native_auth_admin_fidelity | 3 | FAILED failures=2 | 2.5  | 730c1673b0905659 |
| dev | test_native_auth | 5 | OK | 8.3  | c9915b5046c47272 |
| dev | test_native_block_fault_ownership | 6 | OK | 0.2  | 737060b06b6b44ac |
| dev | test_native_bounds_blob | 1 | OK | 1.5  | 4b39b447e6753e93 |
| dev | test_native_bounds_join | 3 | OK | 33.0  | 6d59188804d7a632 |
| dev | test_native_checkpoint | 26 | FAILED failures=1 | 78.2 over | ded84af0c4a7a82c |
| dev | test_native_compaction_crash_map | 4 | OK | 0.1  | 528a36d9abf196ea |
| dev | test_native_consumer_e2 | 4 | OK (skipped=1) | 9.0  | f6a77c4d2cc61818 |
| dev | test_native_consumer_exchange | 8 | OK | 26.7  | 8a9def0a90259ccb |
| dev | test_native_consumer_inspect | 4 | OK | 0.5  | 1b2b81447d082fdf |
| dev | test_native_consumer_project_bounds | 2 | FAILED failures=1 | 0.3  | 4adf4756edf5d759 |
| dev | test_native_control_authority | 1 | OK | 2.6  | 2eb38b9bb614d89c |
| dev | test_native_control_filing | 5 | OK | 16.8  | 2abe0ca11a3d47b9 |
| dev | test_native_control | ? | terminated; whole: stopped (8f0543a1962dfa10) | 180.0 over | 91ea0c1758974363 |
| dev | test_native_crash_correspondence | 8 | OK | 0.1  | e50ced131dd09764 |
| dev | test_native_crash_model | 7 | OK | 49.7 over | da30f23765d0198e |
| dev | test_native_cut_map | 3 | OK | 0.1  | 8d8b0b99c499002c |
| dev | test_native_frozen_relocation | 2 | OK (skipped=2) | 0.1  | 1c244c35aa39a3fa |
| dev | test_native_history_marker | 6 | OK | 5.8  | 9e72b28094e5bfef |
| dev | test_native_history_required | 6 | FAILED failures=1 | 54.3 over | 27a0f96ee072f468 |
| dev | test_native_hybrid_author | 11 | OK | 35.6  | 0953d401d8e72d0b |
| dev | test_native_initializer_fidelity | 11 | OK | 1.6  | 7b8384d26d0eef9e |
| dev | test_native_key_statements | 5 | OK | 17.1  | 57a6dd09b947d1ad |
| dev | test_native_live_reconfiguration | 11 | FAILED failures=3 | 5.0  | 2423f5665689057e |
| dev | test_native_newnews_migration | 1 | OK (skipped=1) | 0.1  | 25a83f535474c39f |
| dev | test_native_nntp_post_probe | 13 | OK | 0.2  | 19a96bf3c1231abd |
| dev | test_native_operator_campaign | 5 | OK | 0.1  | 29d5be86e7ddf908 |
| dev | test_native_operator_cli | 6 | OK | 6.9  | ebea40735709c8e5 |
| dev | test_native_operator_verbs | 22 | FAILED failures=1, errors=1 | 127.7 over | 4dca4c80098867e6 |
| dev | test_native_operator_verdicts | 6 | OK | 12.9  | 9ee2f3134c1cee50 |
| dev | test_native_owner | 18 | FAILED failures=2 | 6.5  | 5500a7ab87830322 |
| dev | test_native_peer_invite | 5 | OK | 14.9  | c91a21ecb06bd462 |
| dev | test_native_peer_pull | 13 | OK (skipped=1) | 112.5 over | 62446c0889d6efcc |
| dev | test_native_peering_matrix_slice | 1 | OK | 0.2  | f88fd0f4e5b4a996 |
| dev | test_native_peering | 5 | OK (skipped=5) | 0.3  | 1bcf59f1ea602e73 |
| dev | test_native_profile_namespace | 1 | OK | 2.3  | 0cdc8b986d476197 |
| dev | test_native_profile_upgrade | 11 | FAILED failures=1 | 24.6  | 64e278005d0b94a6 |
| dev | test_native_profile | 3 | OK | 2.7  | 2eb10673cd4c7673 |
| dev | test_native_program_check | 14 | OK | 0.6  | b5ba525b84082269 |
| dev | test_native_protected_peering | 5 | OK (skipped=5) | 0.4  | a12f7de35a2d43e2 |
| dev | test_native_raw_scripts | 9 | OK | 0.5  | 9549dccd38f75c9c |
| dev | test_native_reader_index | 5 | OK | 13.1  | 233ab8b3c72f76dc |
| dev | test_native_recovery | 13 | OK | 2.2  | 93bafa6d73403e8a |
| dev | test_native_served_cost | 3 | OK | 0.1  | f8dbf44377b762d8 |
| dev | test_native_served_crash_model | ? | terminated; whole: OK (3dd96c3b65b825a5) | 180.0 over | 86cc897bab8f297d |
| dev | test_native_served_differential | 7 | OK | 1.1  | e1ebd76b84172a9e |
| dev | test_native_shared_owner_bench | 2 | OK | 0.1  | db7d6675bb587ff3 |
| dev | test_native_source_corpus | 3 | FAILED failures=1 | 14.0  | 4497d1d922ebd3bc |
| dev | test_native_stamp_migration | 1 | OK (skipped=1) | 0.1  | 7a4cafdaaa3e41ec |
| dev | test_native_starttls | 2 | OK | 1.8  | 520ef86b37835244 |
| dev | test_native_state_checkpoint | 6 | FAILED failures=1 | 106.2 over | 8de4ba5fa7159e2c |
| dev | test_native_storage_codec | 11 | OK | 6.0  | 3f2d17182567ea19 |
| dev | test_native_tls_transport | 2 | OK | 1.0  | e4d50d2174846123 |
| dev | test_native_topic_local | 4 | OK (skipped=2) | 6.0  | e1eb7fcbe3fec179 |
| dev | test_native_topic_metadata | 2 | OK | 1.3  | 0729c35662a5e916 |
| dev | test_native_two_host_protected_gate | 5 | OK | 0.2  | f3653e8906c49d30 |
| dev | test_native_v0_matrix | 67 | FAILED failures=1 | 0.6  | ccc04783a099ba98 |
| dev | test_native_visibility_join | 3 | OK | 12.3  | 4723bc11022aac7f |
| dev | test_native_capacity_vector | 1 | OK | 71.2 over | 5de7395a5bc42fe2 |
| dev | test_native_consumer_exchange_two_nodes | 2 | OK | 19.9  | 5fcd4eaa9261f474 |
| dev | test_native_consumer_profile | 1 | OK | 26.8 over | fd3af7af34c5e5f8 |
| dev | test_native_control_across_peers | 4 | OK | 27.1  | 260fcaa5ce5398b2 |
| dev | test_native_friends_accounts | 1 | OK | 8.2  | 8474cf32d2aa506d |
| dev | test_native_friends_feed | 2 | OK | 5.5  | f7a8c7aac6ab3a72 |
| dev | test_native_implicit_tls | 3 | OK | 3.0  | 57b30d15eac4e955 |
| dev | test_native_outcome_algebra | 9 | FAILED errors=1 | 126.0 over | 16985ee166f73cb4 |
| dev | test_native_pack_chain | ? | terminated; whole: stopped (57b849c79b724b11) | 180.0 over | d22485f51e60fc69 |
| dev | test_native_pre_c1_open | 3 | OK | 0.9  | c79b04936bc72fd8 |
| dev | test_native_public_exposure | 1 | OK | 52.8 over | b2f1eb4733a079df |
| dev | test_native_rollback_history | 5 | OK | 2.3  | d5128dd9ba145db0 |
| dev | test_throughput_gate | 12 | OK | 0.4  | 90300bb2ab0292df |
| dev | test_native_checkpoint_generations | 2 | OK | 0.9  | e51995c1c7f592ef |
| dev | test_native_control_evidence | 1 | OK | 1.7  | 052dc9a147e6acfb |
| dev | test_native_control_reply_fit | 5 | OK | 7.6  | bd12d57ead6214a4 |
| dev | test_native_peer_rows_growth | ? | terminated; whole: stopped (1511644c763bef06) | 180.0 over | 65aca5b01d767392 |
| dtn | test_bp_service_native | 17 | FAILED failures=7 | 9.3  | 06841ea9ceb69fb2 |
| dtn | test_bp_contact_native | 2 | OK | 1.3  | 968d1a4291cfdf71 |
| dtn | test_bp_contact_relay_native | 1 | OK | 3.0  | 3cc7c0885fdfac20 |
| dtn | test_bp_app_native | 7 | OK | 72.4 over | be9adef902cbe04d |
| dtn | test_bp_node_native | 27 | FAILED failures=27 | 21.8  | db7ce4bebb62b7de |
| dtn | test_bp_receive_integrity_native | 4 | FAILED failures=2 | 1.0  | 20ab668be8d2a70e |
| dtn | test_bp_fragment_node_native | ? | terminated; whole: FAILED (errors=1) (e2876d83a60cdc46) | 180.0 over | 9ea696a652600a77 |
| dtn | test_bp_obligation_native | 5 | FAILED failures=1 | 4.1  | 6567f98c40b74d06 |
| dtn | test_native_source_corpus_bp | 1 | OK | 130.1 over | b9914cdf8999e200 |
| dtn | test_native_bp_app_clock | 1 | OK | 0.2  | 3abf81a5170be0c4 |
| dtn | test_native_bp_channel_admission | 1 | OK | 0.1  | f616a079b059caa6 |
| dtn | test_native_bp_node_admission_lock | 1 | OK | 0.1  | 2339765a639b7eeb |
| dtn | test_native_bp_transit_identity | 1 | OK | 0.1  | 2312f526f6b1fdbd |
| dtn | test_native_app_journal | 10 | OK | 4.7  | 8e67c6ee8d272291 |
| dtn | test_native_image_profiles | 12 | OK | 1.7  | 25f1fc27bd055a69 |
| dtndev | test_bp_service_native | 17 | OK | 19.1  | 07a2631fb65df90e |
| dtndev | test_bp_contact_native | 2 | OK | 1.1  | 3468cc9a5512b887 |
| dtndev | test_bp_contact_relay_native | 1 | OK | 2.9  | 53668c9baa106fc1 |
| dtndev | test_bp_app_native | 7 | OK | 14.0  | 8f6ff089df7b7036 |
| dtndev | test_bp_node_native | 27 | OK | 125.6  | fb681cc02ab7ee64 |
| dtndev | test_bp_receive_integrity_native | 4 | OK | 1.3  | 20cd6b001d6188d4 |
| dtndev | test_bp_fragment_node_native | ? | terminated; whole: FAILED (errors=1) (63b91377411519fc) | 180.0 over | 5562b3799befa684 |
| dtndev | test_bp_obligation_native | 5 | FAILED failures=1 | 3.5  | 6dd003ac5dbd84a2 |
| dtndev | test_native_source_corpus_bp | 1 | OK | 138.9 over | 5f266a61b6b77d06 |
| dtndev | test_native_bp_app_clock | 1 | OK | 0.1  | ff335f38c8b296e2 |
| dtndev | test_native_bp_channel_admission | 1 | OK | 0.1  | 759bd0f15fef7b7e |
| dtndev | test_native_bp_node_admission_lock | 1 | OK | 0.1  | c5ba92900ffa976e |
| dtndev | test_native_bp_transit_identity | 1 | OK | 0.2  | 9ecd9b7bbb19881c |
| dtndev | test_native_app_journal | 10 | OK | 6.1  | c5b8a5f8e7ec65a3 |
| dtndev | test_native_image_profiles | 12 | OK | 2.1  | cedfddce5f2c04eb |
