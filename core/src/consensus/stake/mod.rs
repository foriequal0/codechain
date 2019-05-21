// Copyright 2018-2019 Kodebox, Inc.
// This file is part of CodeChain.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as
// published by the Free Software Foundation, either version 3 of the
// License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <https://www.gnu.org/licenses/>.

mod action_data;
mod actions;
mod distribute;

use std::collections::HashMap;
use std::ops::Deref;
use std::sync::Arc;

use ckey::Address;
use cstate::{ActionHandler, StateResult, TopLevelState, TopState};
use ctypes::errors::{RuntimeError, SyntaxError};
use rlp::{Decodable, UntrustedRlp};

use self::action_data::{Candidates, Delegation, StakeAccount, Stakeholders};
use self::actions::Action;
pub use self::distribute::fee_distribute;
use consensus::ValidatorSet;

const CUSTOM_ACTION_HANDLER_ID: u64 = 2;

pub struct Stake {
    genesis_stakes: HashMap<Address, u64>,
    validators: Arc<ValidatorSet>,
    enable_delegations: bool,
}

impl Stake {
    #[cfg(not(test))]
    pub fn new(genesis_stakes: HashMap<Address, u64>, validators: Arc<ValidatorSet>) -> Stake {
        Stake {
            genesis_stakes,
            validators,
            enable_delegations: parse_env_var_enable_delegations(),
        }
    }

    #[cfg(test)]
    pub fn new(genesis_stakes: HashMap<Address, u64>, validators: Arc<ValidatorSet>) -> Stake {
        Stake {
            genesis_stakes,
            validators,
            enable_delegations: true,
        }
    }
}

#[cfg(not(test))]
fn parse_env_var_enable_delegations() -> bool {
    let var = std::env::var("ENABLE_DELEGATIONS");
    match var.as_ref().map(|x| x.trim()) {
        Ok(value) => value.parse::<bool>().unwrap(),
        Err(std::env::VarError::NotPresent) => false,
        Err(err) => unreachable!("{:?}", err),
    }
}

impl ActionHandler for Stake {
    fn handler_id(&self) -> u64 {
        CUSTOM_ACTION_HANDLER_ID
    }

    fn init(&self, state: &mut TopLevelState) -> StateResult<()> {
        let mut stakeholders = Stakeholders::load_from_state(state)?;
        for (address, amount) in self.genesis_stakes.iter() {
            let account = StakeAccount {
                address,
                balance: *amount,
            };
            account.save_to_state(state)?;
            stakeholders.update_by_increased_balance(&account);
        }
        stakeholders.save_to_state(state)?;
        Ok(())
    }

    fn execute(&self, bytes: &[u8], state: &mut TopLevelState, sender: &Address) -> StateResult<()> {
        let action = Action::decode(&UntrustedRlp::new(bytes)).expect("Verification passed");
        match action {
            Action::TransferCCS {
                address,
                quantity,
            } => transfer_ccs(state, sender, &address, quantity),
            Action::DelegateCCS {
                address,
                quantity,
            } => {
                if self.enable_delegations {
                    delegate_ccs(state, sender, &address, quantity, self.validators.deref())
                } else {
                    Err(RuntimeError::FailedToHandleCustomAction("DelegateCCS is disabled".to_string()).into())
                }
            }
            Action::Revoke {
                address,
                quantity,
            } => {
                if self.enable_delegations {
                    revoke(state, sender, &address, quantity)
                } else {
                    Err(RuntimeError::FailedToHandleCustomAction("Revoke is disabled".to_string()).into())
                }
            }
            Action::SelfNominate {
                deposit,
            } => {
                if self.enable_delegations {
                    self_nominate(state, sender, deposit, 0)
                } else {
                    Err(RuntimeError::FailedToHandleCustomAction("SelfNominate is disabled".to_string()).into())
                }
            }
        }
    }

    fn verify(&self, bytes: &[u8]) -> Result<(), SyntaxError> {
        Action::decode(&UntrustedRlp::new(bytes)).map_err(|err| SyntaxError::InvalidCustomAction(err.to_string()))?;
        Ok(())
    }
}

fn transfer_ccs(state: &mut TopLevelState, sender: &Address, receiver: &Address, quantity: u64) -> StateResult<()> {
    let mut stakeholders = Stakeholders::load_from_state(state)?;
    let mut sender_account = StakeAccount::load_from_state(state, sender)?;
    let mut receiver_account = StakeAccount::load_from_state(state, receiver)?;
    let sender_delegations = Delegation::load_from_state(state, sender)?;

    sender_account.subtract_balance(quantity)?;
    receiver_account.add_balance(quantity)?;

    stakeholders.update_by_decreased_balance(&sender_account, &sender_delegations);
    stakeholders.update_by_increased_balance(&receiver_account);

    stakeholders.save_to_state(state)?;
    sender_account.save_to_state(state)?;
    receiver_account.save_to_state(state)?;

    Ok(())
}

fn delegate_ccs(
    state: &mut TopLevelState,
    sender: &Address,
    delegatee: &Address,
    quantity: u64,
    validators: &ValidatorSet,
) -> StateResult<()> {
    // TODO: remove parent hash from validator set.
    if !validators.contains_address(&Default::default(), delegatee) {
        return Err(RuntimeError::FailedToHandleCustomAction("Cannot delegate to non-validator".into()).into())
    }
    let mut delegator = StakeAccount::load_from_state(state, sender)?;
    let mut delegation = Delegation::load_from_state(state, &sender)?;

    delegator.subtract_balance(quantity)?;
    delegation.add_quantity(*delegatee, quantity)?;
    // delegation does not touch stakeholders

    delegation.save_to_state(state)?;
    delegator.save_to_state(state)?;
    Ok(())
}

fn revoke(state: &mut TopLevelState, sender: &Address, delegatee: &Address, quantity: u64) -> StateResult<()> {
    let mut delegator = StakeAccount::load_from_state(state, sender)?;
    let mut delegation = Delegation::load_from_state(state, &sender)?;

    delegator.add_balance(quantity)?;
    delegation.subtract_quantity(*delegatee, quantity)?;
    // delegation does not touch stakeholders

    delegation.save_to_state(state)?;
    delegator.save_to_state(state)?;
    Ok(())
}

fn self_nominate(
    state: &mut TopLevelState,
    sender: &Address,
    deposit: u64,
    nomination_ends_at: u64,
) -> StateResult<()> {
    // TODO: proper handling of get_current_term
    // TODO: proper handling of NOMINATE_EXPIRATION
    // TODO: check banned accounts
    // TODO: check jailed accounts
    let mut deposits = Candidates::load_from_state(&state)?;
    deposits.add_deposit(*sender, deposit, nomination_ends_at);
    state.sub_balance(sender, deposit)?;
    deposits.save_to_state(state)?;
    Ok(())
}

pub fn get_stakes(state: &TopLevelState) -> StateResult<HashMap<Address, u64>> {
    let stakeholders = Stakeholders::load_from_state(state)?;
    let mut result = HashMap::new();
    for stakeholder in stakeholders.iter() {
        let account = StakeAccount::load_from_state(state, stakeholder)?;
        let delegation = Delegation::load_from_state(state, stakeholder)?;
        result.insert(*stakeholder, account.balance + delegation.sum());
    }
    Ok(result)
}

#[allow(dead_code)]
pub fn on_term_close(state: &mut TopLevelState, current_term: u64) -> StateResult<()> {
    // TODO: total_slash = slash_unresponsive(headers, pending_rewards)
    // TODO: pending_rewards.update(signature_reward(blocks, total_slash))

    let mut deposits = Candidates::load_from_state(state)?;
    let expired_candidates = deposits.remove_expired_candidates(current_term);
    for candidate in expired_candidates.into_iter() {
        state.add_balance(&candidate.address, candidate.deposit)?;
    }
    deposits.save_to_state(state)?;

    // TODO: auto_withdraw(pending_rewards)
    // TODO: kick(jailed)

    // TODO: validators, validator_order = elect()
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::action_data::get_account_key;
    use super::*;

    use ckey::{public_to_address, Public};
    use consensus::stake::action_data::get_delegation_key;
    use consensus::validator_set::new_validator_set;
    use cstate::tests::helpers;
    use cstate::TopStateView;
    use rlp::Encodable;

    #[test]
    fn genesis_stakes() {
        let address1 = Address::random();
        let address2 = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(address1, 100);
            Stake::new(genesis_stakes, new_validator_set(Vec::new()))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let account1 = StakeAccount::load_from_state(&state, &address1).unwrap();
        let account2 = StakeAccount::load_from_state(&state, &address2).unwrap();
        assert_eq!(account1.balance, 100);
        assert_eq!(account2.balance, 0);
        let stakeholders = Stakeholders::load_from_state(&state).unwrap();
        assert!(stakeholders.contains(&address1));
        assert!(!stakeholders.contains(&address2));
    }

    #[test]
    fn balance_transfer_partial() {
        let address1 = Address::random();
        let address2 = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(address1, 100);
            Stake::new(genesis_stakes, new_validator_set(Vec::new()))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let result = transfer_ccs(&mut state, &address1, &address2, 10);
        assert_eq!(Ok(()), result);

        let account1 = StakeAccount::load_from_state(&state, &address1).unwrap();
        let account2 = StakeAccount::load_from_state(&state, &address2).unwrap();
        assert_eq!(account1.balance, 90);
        assert_eq!(account2.balance, 10);
        let stakeholders = Stakeholders::load_from_state(&state).unwrap();
        assert!(stakeholders.contains(&address1));
        assert!(stakeholders.contains(&address2));
    }

    #[test]
    fn balance_transfer_all() {
        let address1 = Address::random();
        let address2 = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(address1, 100);
            Stake::new(genesis_stakes, new_validator_set(Vec::new()))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        transfer_ccs(&mut state, &address1, &address2, 100).unwrap();

        let account1 = StakeAccount::load_from_state(&state, &address1).unwrap();
        let account2 = StakeAccount::load_from_state(&state, &address2).unwrap();
        assert_eq!(account1.balance, 0);
        assert_eq!(state.action_data(&get_account_key(&address1)).unwrap(), None);
        assert_eq!(account2.balance, 100);
        let stakeholders = Stakeholders::load_from_state(&state).unwrap();
        assert!(!stakeholders.contains(&address1));
        assert!(stakeholders.contains(&address2));
    }

    #[test]
    fn delegate() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(vec![delegatee_public]))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 40,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert_eq!(result, Ok(()));

        let delegator_account = StakeAccount::load_from_state(&state, &delegator).unwrap();
        let delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        assert_eq!(delegator_account.balance, 60);
        assert_eq!(delegation.iter().count(), 1);
        assert_eq!(delegation.get_quantity(&delegatee), 40);

        // Should not be touched
        let delegatee_account = StakeAccount::load_from_state(&state, &delegatee).unwrap();
        let delegation_untouched = Delegation::load_from_state(&state, &delegatee).unwrap();
        assert_eq!(delegatee_account.balance, 100);
        assert_eq!(delegation_untouched.iter().count(), 0);
    }

    #[test]
    fn delegate_all() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(vec![delegatee_public]))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 100,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert_eq!(result, Ok(()));

        let delegator_account = StakeAccount::load_from_state(&state, &delegator).unwrap();
        let delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        assert_eq!(delegator_account.balance, 0);
        assert_eq!(state.action_data(&get_account_key(&delegator)).unwrap(), None);
        assert_eq!(delegation.iter().count(), 1);
        assert_eq!(delegation.get_quantity(&delegatee), 100);

        // Should not be touched
        let delegatee_account = StakeAccount::load_from_state(&state, &delegatee).unwrap();
        let delegation_untouched = Delegation::load_from_state(&state, &delegatee).unwrap();
        assert_eq!(delegatee_account.balance, 100);
        assert_eq!(delegation_untouched.iter().count(), 0);
    }

    #[test]
    fn delegate_only_to_validator() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(Vec::new()))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 40,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_err());
    }

    #[test]
    fn delegate_too_much() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(vec![delegatee_public]))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 200,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_err());
    }

    #[test]
    fn can_transfer_within_non_delegated_tokens() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(vec![delegatee_public]))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 50,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_ok());

        let action = Action::TransferCCS {
            address: delegatee,
            quantity: 50,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_ok());
    }

    #[test]
    fn cannot_transfer_over_non_delegated_tokens() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(vec![delegatee_public]))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 50,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_ok());

        let action = Action::TransferCCS {
            address: delegatee,
            quantity: 100,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_err());
    }

    #[test]
    fn can_revoke_delegated_tokens() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(vec![delegatee_public]))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 50,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_ok());

        let action = Action::Revoke {
            address: delegatee,
            quantity: 20,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert_eq!(Ok(()), result);

        let delegator_account = StakeAccount::load_from_state(&state, &delegator).unwrap();
        let delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        assert_eq!(delegator_account.balance, 100 - 50 + 20);
        assert_eq!(delegation.iter().count(), 1);
        assert_eq!(delegation.get_quantity(&delegatee), 50 - 20);
    }

    #[test]
    fn cannot_revoke_more_than_delegated_tokens() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(vec![delegatee_public]))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 50,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_ok());

        let action = Action::Revoke {
            address: delegatee,
            quantity: 70,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_err());

        let delegator_account = StakeAccount::load_from_state(&state, &delegator).unwrap();
        let delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        assert_eq!(delegator_account.balance, 100 - 50);
        assert_eq!(delegation.iter().count(), 1);
        assert_eq!(delegation.get_quantity(&delegatee), 50);
    }

    #[test]
    fn revoke_all_should_clear_state() {
        let delegatee_public = Public::random();
        let delegatee = public_to_address(&delegatee_public);
        let delegator = Address::random();

        let mut state = helpers::get_temp_state();
        let stake = {
            let mut genesis_stakes = HashMap::new();
            genesis_stakes.insert(delegatee, 100);
            genesis_stakes.insert(delegator, 100);
            Stake::new(genesis_stakes, new_validator_set(vec![delegatee_public]))
        };
        assert_eq!(Ok(()), stake.init(&mut state));

        let action = Action::DelegateCCS {
            address: delegatee,
            quantity: 50,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert!(result.is_ok());

        let action = Action::Revoke {
            address: delegatee,
            quantity: 50,
        };
        let result = stake.execute(&action.rlp_bytes(), &mut state, &delegator);
        assert_eq!(Ok(()), result);

        let delegator_account = StakeAccount::load_from_state(&state, &delegator).unwrap();
        assert_eq!(delegator_account.balance, 100);
        assert_eq!(state.action_data(&get_delegation_key(&delegator)).unwrap(), None);
    }

    #[test]
    fn self_nominate_deposit_test() {
        let mut state = helpers::get_temp_state();
        let stake = Stake::new(HashMap::new(), new_validator_set(Vec::new()));
        stake.init(&mut state).unwrap();

        let address = Address::random();
        state.add_balance(&address, 1000).unwrap();

        // TODO: change with stake.execute()
        assert_eq!(Ok(()), self_nominate(&mut state, &address, 0, 5));
        assert_eq!(1000, state.balance(&address).unwrap());
        let candidates = Candidates::load_from_state(&state).unwrap();
        let candidate = candidates.get_candidate(address).expect("Candidate should exist even if it deposits 0");
        assert_eq!(0, candidate.deposit);
        assert_eq!(
            5, candidate.nomination_ends_at,
            "nomination_ends_at should be updated even if candidate deposits 0"
        );

        assert_eq!(Ok(()), self_nominate(&mut state, &address, 100, 10));
        assert_eq!(900, state.balance(&address).unwrap());
        let candidates = Candidates::load_from_state(&state).unwrap();
        let candidate = candidates.get_candidate(address).unwrap();
        assert_eq!(100, candidate.deposit);
        assert_eq!(10, candidate.nomination_ends_at);

        assert_eq!(Ok(()), self_nominate(&mut state, &address, 100, 20));
        assert_eq!(800, state.balance(&address).unwrap());
        let candidates = Candidates::load_from_state(&state).unwrap();
        let candidate = candidates.get_candidate(address).unwrap();
        assert_eq!(200, candidate.deposit);
        assert_eq!(20, candidate.nomination_ends_at);

        assert_eq!(Ok(()), self_nominate(&mut state, &address, 0, 30));
        assert_eq!(800, state.balance(&address).unwrap());
        let candidates = Candidates::load_from_state(&state).unwrap();
        let candidate = candidates.get_candidate(address).unwrap();
        assert_eq!(200, candidate.deposit);
        assert_eq!(
            30, candidate.nomination_ends_at,
            "nomination_ends_at should be updated even if candidate deposits 0"
        );

        assert_eq!(Ok(()), on_term_close(&mut state, 20));
        assert_eq!(800, state.balance(&address).unwrap(), "Keep balance before expiration");
        let candidates = Candidates::load_from_state(&state).unwrap();
        let candidate = candidates.get_candidate(address).unwrap();
        assert_eq!(200, candidate.deposit, "Keep deposit before expiration");
        assert_eq!(30, candidate.nomination_ends_at, "Keep expiration before expiration");

        assert_eq!(Ok(()), on_term_close(&mut state, 30));
        assert_eq!(1000, state.balance(&address).unwrap(), "Return deposit after expiration");
        let candidates = Candidates::load_from_state(&state).unwrap();
        assert!(candidates.get_candidate(address).is_none(), "Removed from candidates after expiration");
    }

    #[test]
    fn self_nominate_fail_with_insufficient_balance() {
        let mut state = helpers::get_temp_state();
        let stake = Stake::new(HashMap::new(), new_validator_set(Vec::new()));
        stake.init(&mut state).unwrap();

        let address = Address::random();
        state.add_balance(&address, 1000).unwrap();

        // TODO: change with stake.execute()
        assert!(
            self_nominate(&mut state, &address, 2000, 5).is_err(),
            "Cannot self-nominate without a sufficient balance"
        );
    }
}
