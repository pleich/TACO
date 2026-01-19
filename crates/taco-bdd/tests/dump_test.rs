//! Tests for the dump function of the BDD managers.

#[cfg(all(test, feature = "visualize"))]
mod dump_tests {
    use std::io::Read;

    use taco_bdd::{BDDManager, Bdd, BddManager};

    #[cfg(feature = "visualize")]
    /// This function is a helper function to test the dump function of the BDD manager.
    ///
    /// Note: The test file must be unique for each test, otherwise the tests
    /// will interfere with each other as they are run in parallel by default.
    fn test_dump<T: BddManager>(mut mgr: T, test_file: &str) {
        let var1 = mgr.new_var();
        let var2 = mgr.new_var();
        let var3 = mgr.new_var();

        let node = var1.and(&var2);
        let node = node.or(&var3);

        let file = std::fs::File::create(test_file).unwrap();
        mgr.dump_dot(
            file,
            vec![(&node, "foo")],
            vec![(&var1, "var1"), (&var2, "var2"), (&var3, "var3")],
        )
        .unwrap();

        let mut file = std::fs::File::open(test_file).unwrap();
        let mut content = String::new();
        file.read_to_string(&mut content).unwrap();

        assert!(content.contains("var1"), "{}", content);
        assert!(content.contains("var2"), "{}", content);
        assert!(content.contains("var3"), "{}", content);
        //assert!(content.contains("foo"), "{}", content);

        std::fs::remove_file(test_file).unwrap();
    }

    #[cfg(all(feature = "visualize", feature = "cudd"))]
    #[test]
    fn test_cudd_dump() {
        let mgr = BDDManager::new_cudd();
        test_dump(mgr, "./test_cudd_dump.dot");
    }

    #[cfg(all(feature = "visualize", feature = "oxidd"))]
    #[test]
    fn test_oxidd_dump() {
        let mgr = BDDManager::new_oxidd();
        test_dump(mgr, "./test_oxidd_dump.dot");
    }
}
