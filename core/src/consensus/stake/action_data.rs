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

#[cfg(test)]
use std::collections::btree_map;

use std::collections::btree_map::Entry;

use std::collections::{btree_set, BTreeMap, BTreeSet};

use ckey::Address;
use cstate::{ActionData, ActionDataKeyBuilder, StateResult, TopLevelState, TopState, TopStateView};
use ctypes::errors::RuntimeError;
use primitives::H256;
use rlp::{decode_list, Decodable, Encodable, Rlp, RlpStream};

use super::CUSTOM_ACTION_HANDLER_ID;

pub fn get_account_key(address: &Address) -> H256 {
    ActionDataKeyBuilder::new(CUSTOM_ACTION_HANDLER_ID, 2).append(&"Account").append(address).into_key()
}

lazy_static! {
    pub static ref STAKEHOLDER_ADDRESSES_KEY: H256 =
        ActionDataKeyBuilder::new(CUSTOM_ACTION_HANDLER_ID, 1).append(&"StakeholderAddresses").into_key();
    pub static ref CANDIDATES_KEY: H256 =
        ActionDataKeyBuilder::new(CUSTOM_ACTION_HANDLER_ID, 1).append(&"Candidates").into_key();
}

pub fn get_delegation_key(address: &Address) -> H256 {
    ActionDataKeyBuilder::new(CUSTOM_ACTION_HANDLER_ID, 2).append(&"Delegation").append(address).into_key()
}

pub type StakeQuantity = u64;
pub type Deposit = u64;

pub struct StakeAccount<'a> {
    pub address: &'a Address,
    pub balance: StakeQuantity,
}

impl<'a> StakeAccount<'a> {
    pub fn load_from_state(state: &TopLevelState, address: &'a Address) -> StateResult<StakeAccount<'a>> {
        let account_key = get_account_key(address);
        let action_data = state.action_data(&account_key)?;

        let balance = match action_data {
            Some(data) => Rlp::new(&data).as_val(),
            None => StakeQuantity::default(),
        };

        Ok(StakeAccount {
            address,
            balance,
        })
    }

    pub fn save_to_state(&self, state: &mut TopLevelState) -> StateResult<()> {
        let account_key = get_account_key(self.address);
        if self.balance != 0 {
            let rlp = rlp::encode(&self.balance);
            state.update_action_data(&account_key, rlp.into_vec())?;
        } else {
            state.remove_action_data(&account_key);
        }
        Ok(())
    }

    pub fn subtract_balance(&mut self, amount: u64) -> Result<(), RuntimeError> {
        if self.balance < amount {
            return Err(RuntimeError::InsufficientBalance {
                address: *self.address,
                cost: amount,
                balance: self.balance,
            })
        }
        self.balance -= amount;
        Ok(())
    }

    pub fn add_balance(&mut self, amount: u64) -> Result<(), RuntimeError> {
        self.balance += amount;
        Ok(())
    }
}

pub struct Stakeholders(BTreeSet<Address>);

impl Stakeholders {
    pub fn load_from_state(state: &TopLevelState) -> StateResult<Stakeholders> {
        let action_data = state.action_data(&*STAKEHOLDER_ADDRESSES_KEY)?;
        let addresses = decode_set(action_data.as_ref());
        Ok(Stakeholders(addresses))
    }

    pub fn save_to_state(&self, state: &mut TopLevelState) -> StateResult<()> {
        let key = *STAKEHOLDER_ADDRESSES_KEY;
        if !self.0.is_empty() {
            state.update_action_data(&key, encode_set(&self.0))?;
        } else {
            state.remove_action_data(&key);
        }
        Ok(())
    }

    #[cfg(test)]
    pub fn contains(&self, address: &Address) -> bool {
        self.0.contains(address)
    }

    pub fn update_by_increased_balance(&mut self, account: &StakeAccount) {
        if account.balance > 0 {
            self.0.insert(*account.address);
        }
    }

    pub fn update_by_decreased_balance(&mut self, account: &StakeAccount, delegation: &Delegation) {
        assert!(account.address == delegation.delegator);
        if account.balance == 0 && delegation.sum() == 0 {
            self.0.remove(account.address);
        }
    }

    pub fn iter(&self) -> btree_set::Iter<Address> {
        self.0.iter()
    }
}

pub struct Delegation<'a> {
    pub delegator: &'a Address,
    delegatees: BTreeMap<Address, StakeQuantity>,
}

impl<'a> Delegation<'a> {
    pub fn load_from_state(state: &TopLevelState, delegator: &'a Address) -> StateResult<Delegation<'a>> {
        let key = get_delegation_key(delegator);
        let action_data = state.action_data(&key)?;
        let delegatees = decode_map(action_data.as_ref());

        Ok(Delegation {
            delegator,
            delegatees,
        })
    }

    pub fn save_to_state(&self, state: &mut TopLevelState) -> StateResult<()> {
        let key = get_delegation_key(self.delegator);
        if !self.delegatees.is_empty() {
            let encoded = encode_map(&self.delegatees);
            state.update_action_data(&key, encoded)?;
        } else {
            state.remove_action_data(&key);
        }
        Ok(())
    }

    pub fn add_quantity(&mut self, delegatee: Address, quantity: StakeQuantity) -> StateResult<()> {
        if quantity == 0 {
            return Ok(())
        }
        *self.delegatees.entry(delegatee).or_insert(0) += quantity;
        Ok(())
    }

    pub fn subtract_quantity(&mut self, delegatee: Address, quantity: StakeQuantity) -> StateResult<()> {
        if quantity == 0 {
            return Ok(())
        }

        if let Entry::Occupied(mut entry) = self.delegatees.entry(delegatee) {
            if *entry.get() > quantity {
                *entry.get_mut() -= quantity;
                return Ok(())
            } else if *entry.get() == quantity {
                entry.remove();
                return Ok(())
            }
        }

        Err(RuntimeError::FailedToHandleCustomAction("Cannot subtract more than that is delegated to".to_string())
            .into())
    }

    #[cfg(test)]
    pub fn get_quantity(&self, delegatee: &Address) -> StakeQuantity {
        self.delegatees.get(delegatee).cloned().unwrap_or(0)
    }

    #[cfg(test)]
    pub fn iter(&self) -> btree_map::Iter<Address, StakeQuantity> {
        self.delegatees.iter()
    }

    pub fn sum(&self) -> u64 {
        self.delegatees.values().sum()
    }
}

pub struct Candidates(BTreeMap<Address, Candidate>);
#[derive(RlpEncodable, RlpDecodable, Clone)]
#[cfg_attr(test, derive(Debug, Eq, PartialEq))]
pub struct Candidate {
    pub address: Address,
    pub deposit: Deposit,
    pub nomination_ends_at: u64,
}

impl Candidates {
    pub fn load_from_state(state: &TopLevelState) -> StateResult<Candidates> {
        let key = *CANDIDATES_KEY;
        let candidates = state.action_data(&key)?.map(|data| decode_list::<Candidate>(&data)).unwrap_or_default();
        let indexed = candidates.into_iter().map(|c| (c.address, c)).collect();
        Ok(Candidates(indexed))
    }

    pub fn save_to_state(&self, state: &mut TopLevelState) -> StateResult<()> {
        let key = *CANDIDATES_KEY;
        if !self.0.is_empty() {
            let encoded = encode_iter(self.0.values());
            state.update_action_data(&key, encoded)?;
        } else {
            state.remove_action_data(&key);
        }
        Ok(())
    }

    #[cfg(test)]
    pub fn get_candidate(&self, account: Address) -> Option<&Candidate> {
        self.0.get(&account)
    }

    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn add_deposit(&mut self, address: Address, quantity: Deposit, nomination_ends_at: u64) {
        match self.0.entry(address) {
            Entry::Occupied(mut entry) => {
                let mut candidate = entry.get_mut();
                assert!(
                    candidate.nomination_ends_at <= nomination_ends_at,
                    "nomination_ends_at should not be decreased (existing {}, new {})",
                    candidate.nomination_ends_at,
                    nomination_ends_at
                );
                candidate.deposit += quantity;
                candidate.nomination_ends_at = nomination_ends_at;
            }
            Entry::Vacant(entry) => {
                entry.insert(Candidate {
                    address,
                    deposit: quantity,
                    nomination_ends_at,
                });
            }
        }
    }

    #[allow(dead_code)]
    pub fn remove_expired_candidates(&mut self, term_index: u64) -> Vec<Candidate> {
        let (expired, retained): (Vec<_>, Vec<_>) =
            self.0.values().cloned().partition(|c| c.nomination_ends_at <= term_index);
        self.0 = retained.into_iter().map(|c| (c.address, c)).collect();
        expired
    }
}

fn decode_set<V>(data: Option<&ActionData>) -> BTreeSet<V>
where
    V: Ord + Decodable, {
    let mut result = BTreeSet::new();
    if let Some(rlp) = data.map(|x| Rlp::new(x)) {
        for record in rlp.iter() {
            let value: V = record.as_val();
            result.insert(value);
        }
    }
    result
}

fn encode_set<V>(set: &BTreeSet<V>) -> Vec<u8>
where
    V: Ord + Encodable, {
    let mut rlp = RlpStream::new();
    rlp.begin_list(set.len());
    for value in set.iter() {
        rlp.append(value);
    }
    rlp.drain().into_vec()
}

fn decode_map<K, V>(data: Option<&ActionData>) -> BTreeMap<K, V>
where
    K: Ord + Decodable,
    V: Decodable, {
    let mut result = BTreeMap::new();
    if let Some(rlp) = data.map(|x| Rlp::new(x)) {
        for record in rlp.iter() {
            let key: K = record.val_at(0);
            let value: V = record.val_at(1);
            assert_eq!(2, record.item_count());
            result.insert(key, value);
        }
    }
    result
}

fn encode_map<K, V>(map: &BTreeMap<K, V>) -> Vec<u8>
where
    K: Ord + Encodable,
    V: Encodable, {
    let mut rlp = RlpStream::new();
    rlp.begin_list(map.len());
    for (key, value) in map.iter() {
        let mut record = rlp.begin_list(2);
        record.append(key);
        record.append(value);
    }
    rlp.drain().into_vec()
}

fn encode_iter<'a, V, I>(iter: I) -> Vec<u8>
where
    V: 'a + Encodable,
    I: ExactSizeIterator<Item = &'a V> + Clone, {
    let mut rlp = RlpStream::new();
    rlp.begin_list(iter.clone().count());
    for value in iter {
        rlp.append(value);
    }
    rlp.drain().into_vec()
}

#[cfg(test)]
mod tests {
    use super::*;
    use cstate::tests::helpers;
    use rand::{Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;
    use std::collections::HashMap;

    fn rng() -> XorShiftRng {
        let seed: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7];
        XorShiftRng::from_seed(seed)
    }

    #[test]
    fn default_balance_is_zero() {
        let state = helpers::get_temp_state();
        let address = Address::random();
        let account = StakeAccount::load_from_state(&state, &address).unwrap();
        assert_eq!(account.address, &address);
        assert_eq!(account.balance, 0);
    }

    #[test]
    fn balance_add() {
        let mut state = helpers::get_temp_state();
        let address = Address::random();
        {
            let mut account = StakeAccount::load_from_state(&state, &address).unwrap();
            account.add_balance(100).unwrap();
            account.save_to_state(&mut state).unwrap();
        }
        let account = StakeAccount::load_from_state(&state, &address).unwrap();
        assert_eq!(account.balance, 100);
    }

    #[test]
    fn balance_subtract_error_on_low() {
        let mut state = helpers::get_temp_state();
        let address = Address::random();
        {
            let mut account = StakeAccount::load_from_state(&state, &address).unwrap();
            account.add_balance(100).unwrap();
            account.save_to_state(&mut state).unwrap();
        }
        {
            let mut account = StakeAccount::load_from_state(&state, &address).unwrap();
            let result = account.subtract_balance(110);
            assert!(result.is_err());
            assert_eq!(
                result,
                Err(RuntimeError::InsufficientBalance {
                    address,
                    cost: 110,
                    balance: 100,
                })
            );
        }
        let account = StakeAccount::load_from_state(&state, &address).unwrap();
        assert_eq!(account.balance, 100);
    }

    #[test]
    fn balance_subtract() {
        let mut state = helpers::get_temp_state();
        let address = Address::random();

        let mut account = StakeAccount::load_from_state(&state, &address).unwrap();
        account.add_balance(100).unwrap();
        account.save_to_state(&mut state).unwrap();

        let mut account = StakeAccount::load_from_state(&state, &address).unwrap();
        let result = account.subtract_balance(90);
        assert!(result.is_ok());
        account.save_to_state(&mut state).unwrap();

        let account = StakeAccount::load_from_state(&state, &address).unwrap();
        assert_eq!(account.balance, 10);
    }

    #[test]
    fn balance_subtract_all_should_remove_entry_from_db() {
        let mut state = helpers::get_temp_state();
        let address = Address::random();

        let mut account = StakeAccount::load_from_state(&state, &address).unwrap();
        account.add_balance(100).unwrap();
        account.save_to_state(&mut state).unwrap();

        let mut account = StakeAccount::load_from_state(&state, &address).unwrap();
        let result = account.subtract_balance(100);
        assert!(result.is_ok());
        account.save_to_state(&mut state).unwrap();

        let data = state.action_data(&get_account_key(&address)).unwrap();
        assert_eq!(data, None);
    }

    #[test]
    fn stakeholders_track() {
        let mut rng = rng();
        let mut state = helpers::get_temp_state();
        let addresses: Vec<_> = (1..100).map(|_| Address::random()).collect();
        let accounts: Vec<_> = addresses
            .iter()
            .map(|address| StakeAccount {
                address,
                balance: rng.gen_range(1, 100),
            })
            .collect();

        let mut stakeholders = Stakeholders::load_from_state(&state).unwrap();
        for account in &accounts {
            stakeholders.update_by_increased_balance(account);
        }
        stakeholders.save_to_state(&mut state).unwrap();

        let stakeholders = Stakeholders::load_from_state(&state).unwrap();
        assert!(addresses.iter().all(|address| stakeholders.contains(address)));
    }

    #[test]
    fn stakeholders_untrack() {
        let mut rng = rng();
        let mut state = helpers::get_temp_state();
        let addresses: Vec<_> = (1..100).map(|_| Address::random()).collect();
        let mut accounts: Vec<_> = addresses
            .iter()
            .map(|address| StakeAccount {
                address,
                balance: rng.gen_range(1, 100),
            })
            .collect();

        let mut stakeholders = Stakeholders::load_from_state(&state).unwrap();
        for account in &accounts {
            stakeholders.update_by_increased_balance(account);
        }
        stakeholders.save_to_state(&mut state).unwrap();

        let mut stakeholders = Stakeholders::load_from_state(&state).unwrap();
        for account in &mut accounts {
            if rand::random() {
                account.balance = 0;
            }
            let delegation = Delegation::load_from_state(&state, account.address).unwrap();
            stakeholders.update_by_decreased_balance(account, &delegation);
        }
        stakeholders.save_to_state(&mut state).unwrap();

        let stakeholders = Stakeholders::load_from_state(&state).unwrap();
        for account in &accounts {
            let tracked = stakeholders.contains(account.address);
            let has_balance = account.balance > 0;
            assert!(tracked && has_balance || !tracked && !has_balance);
        }
    }

    #[test]
    fn stakeholders_doesnt_untrack_if_delegation_exists() {
        let mut state = helpers::get_temp_state();
        let addresses: Vec<_> = (1..100).map(|_| Address::random()).collect();
        let mut accounts: Vec<_> = addresses
            .iter()
            .map(|address| StakeAccount {
                address,
                balance: 100,
            })
            .collect();

        let mut stakeholders = Stakeholders::load_from_state(&state).unwrap();
        for account in &accounts {
            stakeholders.update_by_increased_balance(account);
        }
        stakeholders.save_to_state(&mut state).unwrap();

        let mut stakeholders = Stakeholders::load_from_state(&state).unwrap();
        for account in &mut accounts {
            // like self-delegate
            let mut delegation = Delegation::load_from_state(&state, account.address).unwrap();
            delegation.add_quantity(*account.address, account.balance).unwrap();
            account.balance = 0;
            stakeholders.update_by_decreased_balance(account, &delegation);
        }
        stakeholders.save_to_state(&mut state).unwrap();

        let stakeholders = Stakeholders::load_from_state(&state).unwrap();
        for account in &accounts {
            assert!(stakeholders.contains(account.address));
        }
    }

    #[test]
    fn initial_delegation_is_empty() {
        let state = helpers::get_temp_state();

        let delegatee = Address::random();
        let delegation = Delegation::load_from_state(&state, &delegatee).unwrap();
        assert_eq!(delegation.delegator, &delegatee);
        assert_eq!(delegation.iter().count(), 0);
    }

    #[test]
    fn delegation_add() {
        let mut rng = rng();
        let mut state = helpers::get_temp_state();

        // Prepare
        let delegator = Address::random();
        let delegatees: Vec<_> = (0..10).map(|_| Address::random()).collect();
        let delegation_amount: HashMap<&Address, StakeQuantity> =
            delegatees.iter().map(|address| (address, rng.gen_range(0, 100))).collect();

        // Do delegate
        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        for delegatee in delegatees.iter() {
            delegation.add_quantity(*delegatee, delegation_amount[delegatee]).unwrap()
        }
        delegation.save_to_state(&mut state).unwrap();

        // assert
        let delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        assert_eq!(delegation.iter().count(), delegatees.len());
        for delegatee in delegatees.iter() {
            assert_eq!(delegation.get_quantity(delegatee), delegation_amount[delegatee]);
        }
    }

    #[test]
    fn delegation_zero_add_should_not_be_included() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let delegator = Address::random();
        let delegatee1 = Address::random();
        let delegatee2 = Address::random();

        // Do delegate
        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        delegation.add_quantity(delegatee1, 100).unwrap();
        delegation.add_quantity(delegatee2, 0).unwrap();
        delegation.save_to_state(&mut state).unwrap();

        let delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        let delegated = delegation.iter().collect::<Vec<_>>();
        assert_eq!(&delegated, &[(&delegatee1, &100)]);
    }

    #[test]
    fn delegation_can_subtract() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let delegator = Address::random();
        let delegatee = Address::random();

        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        delegation.add_quantity(delegatee, 100).unwrap();
        delegation.save_to_state(&mut state).unwrap();

        // Do subtract
        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        delegation.subtract_quantity(delegatee, 30).unwrap();
        delegation.save_to_state(&mut state).unwrap();

        // Assert
        let delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        assert_eq!(delegation.get_quantity(&delegatee), 70);
    }

    #[test]
    fn delegation_cannot_subtract_mor_than_delegated() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let delegator = Address::random();
        let delegatee = Address::random();

        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        delegation.add_quantity(delegatee, 100).unwrap();
        delegation.save_to_state(&mut state).unwrap();

        // Do subtract
        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        assert!(delegation.subtract_quantity(delegatee, 130).is_err());
    }

    #[test]
    fn delegation_empty_removed_from_state() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let delegator = Address::random();
        let delegatee = Address::random();

        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        delegation.add_quantity(delegatee, 0).unwrap();
        delegation.save_to_state(&mut state).unwrap();

        let result = state.action_data(&get_delegation_key(&delegator)).unwrap();
        assert_eq!(result, None);
    }

    #[test]
    fn delegation_became_empty_removed_from_state() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let delegator = Address::random();
        let delegatee = Address::random();

        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        delegation.add_quantity(delegatee, 100).unwrap();
        delegation.save_to_state(&mut state).unwrap();

        // Do subtract
        let mut delegation = Delegation::load_from_state(&state, &delegator).unwrap();
        delegation.subtract_quantity(delegatee, 100).unwrap();
        delegation.save_to_state(&mut state).unwrap();

        // Assert
        let result = state.action_data(&get_delegation_key(&delegator)).unwrap();
        assert_eq!(result, None);
    }

    #[test]
    fn candidates_deposit_add() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let account = Address::random();
        let deposits = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        for deposit in deposits.iter().cloned() {
            let mut candidates = Candidates::load_from_state(&state).unwrap();
            candidates.add_deposit(account, deposit, 0);
            candidates.save_to_state(&mut state).unwrap();
        }

        // Assert
        let candidates = Candidates::load_from_state(&state).unwrap();
        let candidate = candidates.get_candidate(account);
        assert!(candidate.is_some());
        assert_eq!(candidate.unwrap().deposit, 55);
    }

    #[test]
    fn candidates_deposit_can_be_zero() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let account = Address::random();
        let mut candidates = Candidates::load_from_state(&state).unwrap();
        candidates.add_deposit(account, 0, 10);
        candidates.save_to_state(&mut state).unwrap();

        // Assert
        let candidates = Candidates::load_from_state(&state).unwrap();
        let candidate = candidates.get_candidate(account);
        assert!(candidate.is_some());
        assert_eq!(candidate.unwrap().deposit, 0);
        assert_eq!(candidate.unwrap().nomination_ends_at, 10, "Can be a candidate with 0 deposit");
    }

    #[test]
    fn candidates_deposit_should_update_nomination_ends_at() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let account = Address::random();
        let deposit_and_nomination_ends_at = [(10, 11), (20, 22), (30, 33), (0, 44)];

        for (deposit, nomination_ends_at) in deposit_and_nomination_ends_at.iter().cloned() {
            let mut candidates = Candidates::load_from_state(&state).unwrap();
            candidates.add_deposit(account, deposit, nomination_ends_at);
            candidates.save_to_state(&mut state).unwrap();
        }

        // Assert
        let candidates = Candidates::load_from_state(&state).unwrap();
        let candidate = candidates.get_candidate(account);
        assert!(candidate.is_some());
        assert_eq!(candidate.unwrap().deposit, 60);
        assert_eq!(
            candidate.unwrap().nomination_ends_at,
            44,
            "nomination_ends_at should be updated incrementally, and including zero deposit"
        );
    }

    #[test]
    fn candidates_can_remove_expired_deposit() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let candidates_prepared = [
            Candidate {
                address: Address::from(0),
                deposit: 20,
                nomination_ends_at: 11,
            },
            Candidate {
                address: Address::from(1),
                deposit: 30,
                nomination_ends_at: 22,
            },
            Candidate {
                address: Address::from(2),
                deposit: 40,
                nomination_ends_at: 33,
            },
            Candidate {
                address: Address::from(3),
                deposit: 50,
                nomination_ends_at: 44,
            },
        ];

        for Candidate {
            address,
            deposit,
            nomination_ends_at,
        } in candidates_prepared.iter().cloned()
        {
            let mut candidates = Candidates::load_from_state(&state).unwrap();
            candidates.add_deposit(address, deposit, nomination_ends_at);
            candidates.save_to_state(&mut state).unwrap();
        }

        // Remove Expired
        let mut candidates = Candidates::load_from_state(&state).unwrap();
        let expired = candidates.remove_expired_candidates(22);
        candidates.save_to_state(&mut state).unwrap();

        // Assert
        assert_eq!(expired[..], candidates_prepared[0..=1],);
        let candidates = Candidates::load_from_state(&state).unwrap();
        assert_eq!(candidates.len(), 2);
        assert_eq!(candidates.get_candidate(candidates_prepared[2].address), Some(&candidates_prepared[2]));
        assert_eq!(candidates.get_candidate(candidates_prepared[3].address), Some(&candidates_prepared[3]));
    }

    #[test]
    fn candidates_expire_all_cleanup_state() {
        let mut state = helpers::get_temp_state();

        // Prepare
        let candidates_prepared = [
            Candidate {
                address: Address::from(0),
                deposit: 20,
                nomination_ends_at: 11,
            },
            Candidate {
                address: Address::from(1),
                deposit: 30,
                nomination_ends_at: 22,
            },
            Candidate {
                address: Address::from(2),
                deposit: 40,
                nomination_ends_at: 33,
            },
            Candidate {
                address: Address::from(3),
                deposit: 50,
                nomination_ends_at: 44,
            },
        ];

        for Candidate {
            address,
            deposit,
            nomination_ends_at,
        } in candidates_prepared.iter().cloned()
        {
            let mut candidates = Candidates::load_from_state(&state).unwrap();
            candidates.add_deposit(address, deposit, nomination_ends_at);
            candidates.save_to_state(&mut state).unwrap();
        }

        // Remove Expired
        let mut candidates = Candidates::load_from_state(&state).unwrap();
        let expired = candidates.remove_expired_candidates(99);
        candidates.save_to_state(&mut state).unwrap();

        // Assert
        assert_eq!(expired[..], candidates_prepared[0..4]);
        let result = state.action_data(&*CANDIDATES_KEY).unwrap();
        assert_eq!(result, None);
    }
}
