//! Test interaction with the SMT solver.

mod replay_file_tests {
    use std::{fs::File, io::Read};

    use easy_smt::Response;
    use taco_smt_encoder::SMTSolverBuilder;

    const REPLAY_FILE: &str = "../../target/test_replay_file.smt2";

    #[test]
    fn test_replay_file() {
        let replay_file = File::create(REPLAY_FILE).unwrap();

        {
            let mut builder =
                SMTSolverBuilder::new_automatic_selection().expect("Failed to create SMT solver");

            let mut solver = builder.new_solver_with_replay(replay_file);

            let i = solver.int_sort();
            let x = solver.declare_const("x", i).unwrap();

            let constr = solver.and(
                solver.lte(x, solver.numeral(2)),
                solver.gt(x, solver.numeral(1)),
            );
            solver.assert(constr).unwrap();
            assert_eq!(solver.check().unwrap(), Response::Sat);
        }

        let mut content = String::new();
        let _ = File::open(REPLAY_FILE)
            .unwrap()
            .read_to_string(&mut content)
            .unwrap();

        assert!(
            content
                .contains("(declare-const x Int)\n(assert (and (<= x 2) (> x 1)))\n(check-sat)\n")
        );

        std::fs::remove_file(REPLAY_FILE).unwrap();
    }
}
