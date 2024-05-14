// SPDX-License-Identifier: MIT
pragma solidity ^0.8.8;
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract CarbToken is ERC20("Carb Token", "CRB") {

    function mint(uint256 _amount) public {
        _mint(0xb035f574A147F8e3C3203369F92fE9165d17cD96, _amount);
    }

}