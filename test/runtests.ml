open OUnit2

let suite = "test">:::[
    "test_pp">::: Test_pp.suite;
  ]

let () = run_test_tt_main suite
