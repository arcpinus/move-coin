/// Module implementing an odd coin, where only odd number of coins can be
/// transferred each time.
module NamedAddr::OddCoin {
    use std::signer;
    use NamedAddr::MoveCoin;

    struct OddCoin has drop {}

    const ENOT_ODD: u64 = 0;

    public fun setup_and_mint(account: &signer, amount: u64) {
        MoveCoin::publish_balance<OddCoin>(account);
        MoveCoin::mint<OddCoin>(signer::address_of(account), amount, OddCoin {});
    }

    public fun transfer(from: &signer, to: address, amount: u64) {
        // amount must be odd.
        assert!(amount % 2 == 1, ENOT_ODD);
        MoveCoin::transfer<OddCoin>(from, to, amount, OddCoin {});
    }

    /*
        Unit tests
    */
    #[test(from = @0x42, to = @0x10)]
    fun test_odd_success(from: signer, to: signer) {
        setup_and_mint(&from, 42);
        setup_and_mint(&to, 10);

        // transfer an odd number of coins so this should succeed.
        transfer(&from, @0x10, 7);

        assert!(MoveCoin::balance_of<OddCoin>(@0x42) == 35, 0);
        assert!(MoveCoin::balance_of<OddCoin>(@0x10) == 17, 0);
    }

    #[test(from = @0x42, to = @0x10)]
    #[expected_failure]
    fun test_not_odd_failure(from: signer, to: signer) {
        setup_and_mint(&from, 42);
        setup_and_mint(&to, 10);

        // transfer an even number of coins so this should fail.
        transfer(&from, @0x10, 8);
    }
}
