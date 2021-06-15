
// File: contracts/interfaces/IUniswapV2Callee.sol

pragma solidity =0.4.17;

interface IUniswapV2Callee {
	function uniswapV2Call(address sender, uint amount0, uint amount1, bytes data) external;
}

// File: contracts/interfaces/IERC20.sol


interface IERC20 {
	event Approval(address indexed owner, address indexed spender, uint value);
	event Transfer(address indexed from, address indexed to, uint value);

	function name() external view returns (string memory);
	function symbol() external view returns (string memory);
	function decimals() external view returns (uint8);
	function totalSupply() external view returns (uint);
	function balanceOf(address owner) external view returns (uint);
	function allowance(address owner, address spender) external view returns (uint);

	function approve(address spender, uint value) external returns (bool);
	function transfer(address to, uint value) external returns (bool);
	function transferFrom(address from, address to, uint value) external returns (bool);
}

// File: contracts/libraries/UQ112x112.sol


// a library for handling binary fixed point numbers (https://en.wikipedia.org/wiki/Q_(number_format))

// range: [0, 2**112 - 1]
// resolution: 1 / 2**112

library UQ112x112 {
	uint224 constant Q112 = 2**112;

	// encode a uint112 as a UQ112x112
	function encode(uint112 y) internal pure returns (uint224 z) {
		z = uint224(y) * Q112; // never overflows
	}

	// divide a UQ112x112 by a uint112, returning a UQ112x112
	function uqdiv(uint224 x, uint112 y) internal pure returns (uint224 z) {
		z = x / uint224(y);
	}
}

// File: contracts/libraries/Math.sol


// a library for performing various math operations

library Math {
	function min(uint x, uint y) internal pure returns (uint z) {
		z = x < y ? x : y;
	}

	// babylonian method (https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method)
	function sqrt(uint y) internal pure returns (uint z) {
		if (y > 3) {
			z = y;
			uint x = y / 2 + 1;
			while (x < z) {
				z = x;
				x = (y / x + x) / 2;
			}
		} else if (y != 0) {
			z = 1;
		}
	}
}

// File: contracts/libraries/SafeMath.sol


// a library for performing overflow-safe math, courtesy of DappHub (https://github.com/dapphub/ds-math)

library SafeMath {
	/**
	* @dev Multiplies two numbers, reverts on overflow.
	*/
	function mul(uint256 a, uint256 b) internal pure returns (uint256) {
		// Gas optimization: this is cheaper than requiring 'a' not being zero, but the
		// benefit is lost if 'b' is also tested.
		// See: https://github.com/OpenZeppelin/openzeppelin-solidity/pull/522
		if (a == 0) {
			return 0;
		}

		uint256 c = a * b;
		require(c / a == b);

		return c;
	}

	/**
	* @dev Integer division of two numbers truncating the quotient, reverts on division by zero.
	*/
	function div(uint256 a, uint256 b) internal pure returns (uint256) {
		// Solidity only automatically asserts when dividing by 0
		require(b > 0);
		uint256 c = a / b;
		// assert(a == b * c + a % b); // There is no case in which this doesn't hold

		return c;
	}

	/**
	* @dev Subtracts two numbers, reverts on overflow (i.e. if subtrahend is greater than minuend).
	*/
	function sub(uint256 a, uint256 b) internal pure returns (uint256) {
		require(b <= a);
		uint256 c = a - b;

		return c;
	}

	/**
	* @dev Adds two numbers, reverts on overflow.
	*/
	function add(uint256 a, uint256 b) internal pure returns (uint256) {
		uint256 c = a + b;
		require(c >= a);

		return c;
	}

	/**
	* @dev Divides two numbers and returns the remainder (unsigned integer modulo),
	* reverts when dividing by zero.
	*/
	function mod(uint256 a, uint256 b) internal pure returns (uint256) {
		require(b != 0);
		return a % b;
	}
}

// File: contracts/interfaces/IUniswapV2ERC20.sol


interface IUniswapV2ERC20 {
	event Approval(address indexed owner, address indexed spender, uint value);
	event Transfer(address indexed from, address indexed to, uint value);

	function name() external pure returns (string memory);
	function symbol() external pure returns (string memory);
	function decimals() external pure returns (uint8);
	function totalSupply() external view returns (uint);
	function balanceOf(address owner) external view returns (uint);
	function allowance(address owner, address spender) external view returns (uint);

	function approve(address spender, uint value) external returns (bool);
	function transfer(address to, uint value) external returns (bool);
	function transferFrom(address from, address to, uint value) external returns (bool);
}

// File: contracts/UniswapV2ERC20.sol


contract UniswapV2ERC20 is IUniswapV2ERC20 {
	using SafeMath for uint256;

	mapping (address => uint256) internal _balances;

	mapping (address => mapping (address => uint256)) private _allowed;

	uint256 internal _totalSupply;

	/**
	* @dev Total number of tokens in existence
	*/
	function totalSupply() external view returns (uint256) {
		return _totalSupply;
	}

	/**
	* @dev Gets the balance of the specified address.
	* @param owner The address to query the balance of.
	* @return An uint256 representing the amount owned by the passed address.
	*/
	function balanceOf(address owner) external view returns (uint256) {
		return _balances[owner];
	}

	/**
	 * @dev Function to check the amount of tokens that an owner allowed to a spender.
	 * @param owner address The address which owns the funds.
	 * @param spender address The address which will spend the funds.
	 * @return A uint256 specifying the amount of tokens still available for the spender.
	 */
	function allowance(address owner, address spender) external view returns (uint256) {
		return _allowed[owner][spender];
	}

	/**
	* @dev Transfer token for a specified address
	* @param to The address to transfer to.
	* @param value The amount to be transferred.
	*/
	function transfer(address to, uint256 value) external returns (bool) {
		_transfer(msg.sender, to, value);
		return true;
	}

	/**
	 * @dev Approve the passed address to spend the specified amount of tokens on behalf of msg.sender.
	 * Beware that changing an allowance with this method brings the risk that someone may use both the old
	 * and the new allowance by unfortunate transaction ordering. One possible solution to mitigate this
	 * race condition is to first reduce the spender's allowance to 0 and set the desired value afterwards:
	 * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
	 * @param spender The address which will spend the funds.
	 * @param value The amount of tokens to be spent.
	 */
	function approve(address spender, uint256 value) external returns (bool) {
		require(spender != address(0));

		_allowed[msg.sender][spender] = value;
		Approval(msg.sender, spender, value);
		return true;
	}

	/**
	 * @dev Transfer tokens from one address to another.
	 * Note that while this function emits an Approval event, this is not required as per the specification,
	 * and other compliant implementations may not emit the event.
	 * @param from address The address which you want to send tokens from
	 * @param to address The address which you want to transfer to
	 * @param value uint256 the amount of tokens to be transferred
	 */
	function transferFrom(address from, address to, uint256 value) external returns (bool) {
		_allowed[from][msg.sender] = _allowed[from][msg.sender].sub(value);
		_transfer(from, to, value);
		Approval(from, msg.sender, _allowed[from][msg.sender]);
		return true;
	}

	/**
	 * @dev Increase the amount of tokens that an owner allowed to a spender.
	 * approve should be called when allowed_[_spender] == 0. To increment
	 * allowed value is better to use this function to avoid 2 calls (and wait until
	 * the first transaction is mined)
	 * From MonolithDAO Token.sol
	 * Emits an Approval event.
	 * @param spender The address which will spend the funds.
	 * @param addedValue The amount of tokens to increase the allowance by.
	 */
	function increaseAllowance(address spender, uint256 addedValue) public returns (bool) {
		require(spender != address(0));

		_allowed[msg.sender][spender] = _allowed[msg.sender][spender].add(addedValue);
		Approval(msg.sender, spender, _allowed[msg.sender][spender]);
		return true;
	}

	/**
	 * @dev Decrease the amount of tokens that an owner allowed to a spender.
	 * approve should be called when allowed_[_spender] == 0. To decrement
	 * allowed value is better to use this function to avoid 2 calls (and wait until
	 * the first transaction is mined)
	 * From MonolithDAO Token.sol
	 * Emits an Approval event.
	 * @param spender The address which will spend the funds.
	 * @param subtractedValue The amount of tokens to decrease the allowance by.
	 */
	function decreaseAllowance(address spender, uint256 subtractedValue) public returns (bool) {
		require(spender != address(0));

		_allowed[msg.sender][spender] = _allowed[msg.sender][spender].sub(subtractedValue);
		Approval(msg.sender, spender, _allowed[msg.sender][spender]);
		return true;
	}

	/**
	* @dev Transfer token for a specified addresses
	* @param from The address to transfer from.
	* @param to The address to transfer to.
	* @param value The amount to be transferred.
	*/
	function _transfer(address from, address to, uint256 value) internal {
		require(to != address(0));

		_balances[from] = _balances[from].sub(value);
		_balances[to] = _balances[to].add(value);
		Transfer(from, to, value);
	}

	/**
	 * @dev Internal function that mints an amount of the token and assigns it to
	 * an account. This encapsulates the modification of balances such that the
	 * proper events are emitted.
	 * @param account The account that will receive the created tokens.
	 * @param value The amount that will be created.
	 */
	function _mint(address account, uint256 value) internal {
		require(account != address(0));

		_totalSupply = _totalSupply.add(value);
		_balances[account] = _balances[account].add(value);
		Transfer(address(0), account, value);
	}

	/**
	 * @dev Internal function that burns an amount of the token of a given
	 * account.
	 * @param account The account whose tokens will be burnt.
	 * @param value The amount that will be burnt.
	 */
	function _burn(address account, uint256 value) internal {
		require(account != address(0));

		_totalSupply = _totalSupply.sub(value);
		_balances[account] = _balances[account].sub(value);
		Transfer(account, address(0), value);
	}

	/**
	 * @dev Internal function that burns an amount of the token of a given
	 * account, deducting from the sender's allowance for said account. Uses the
	 * internal burn function.
	 * Emits an Approval event (reflecting the reduced allowance).
	 * @param account The account whose tokens will be burnt.
	 * @param value The amount that will be burnt.
	 */
	function _burnFrom(address account, uint256 value) internal {
		_allowed[account][msg.sender] = _allowed[account][msg.sender].sub(value);
		_burn(account, value);
		Approval(account, msg.sender, _allowed[account][msg.sender]);
	}
	/**
	 * @return the name of the token.
	 */
	function name() external pure returns (string) {
		return "Uniswap Token for MintME";
	}

	/**
	 * @return the symbol of the token.
	 */
	function symbol() external pure returns (string) {
		return "UNI-V2";
	}

	/**
	 * @return the number of decimals of the token.
	 */
	function decimals() external pure returns (uint8) {
		return 18;
	}
	
}

// File: contracts/interfaces/IUniswapV2Pair.sol


interface IUniswapV2Pair {
	event Approval(address indexed owner, address indexed spender, uint value);
	event Transfer(address indexed from, address indexed to, uint value);

	function name() external pure returns (string memory);
	function symbol() external pure returns (string memory);
	function decimals() external pure returns (uint8);
	function totalSupply() external view returns (uint);
	function balanceOf(address owner) external view returns (uint);
	function allowance(address owner, address spender) external view returns (uint);

	function approve(address spender, uint value) external returns (bool);
	function transfer(address to, uint value) external returns (bool);
	function transferFrom(address from, address to, uint value) external returns (bool);

	event Mint(address indexed sender, uint amount0, uint amount1);
	event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
	event Swap(
		address indexed sender,
		uint amount0In,
		uint amount1In,
		uint amount0Out,
		uint amount1Out,
		address indexed to
	);
	event Sync(uint112 reserve0, uint112 reserve1);

	function MINIMUM_LIQUIDITY() external pure returns (uint);
	function factory() external view returns (address);
	function token0() external view returns (address);
	function token1() external view returns (address);
	function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);
	function price0CumulativeLast() external view returns (uint);
	function price1CumulativeLast() external view returns (uint);
	function kLast() external view returns (uint);

	function mint(address to) external returns (uint liquidity);
	function burn(address to) external returns (uint amount0, uint amount1);
	function swap(uint amount0Out, uint amount1Out, address to, bytes data) external;
	function skim(address to) external;
	function sync() external;

	function initialize(address, address) external;
}

// File: contracts/UniswapV2Pair.sol









contract UniswapV2Pair is IUniswapV2Pair, UniswapV2ERC20 {
	using SafeMath  for uint;
	using UQ112x112 for uint224;

	function MINIMUM_LIQUIDITY() external pure returns (uint256){
		return 10**3;
	}
	bytes4 private constant SELECTOR = bytes4(0xa9059cbb);

	address public factory;
	function factory() external view returns (address){
		return factory;
	}
	address public token0;
	function token0() external view returns (address){
		return token0;
	}
	address public token1;
	function token1() external view returns (address){
		return token1;
	}
	uint112 private reserve0;		   // uses single storage slot, accessible via getReserves
	uint112 private reserve1;		   // uses single storage slot, accessible via getReserves
	uint32  private blockTimestampLast; // uses single storage slot, accessible via getReserves

	uint public price0CumulativeLast;
	function price0CumulativeLast() external view returns (uint){
		return price0CumulativeLast;
	}
	uint public price1CumulativeLast;
	function price1CumulativeLast() external view returns (uint){
		return price1CumulativeLast;
	}
	uint public kLast; // reserve0 * reserve1, as of immediately after the most recent liquidity event
	function kLast() external view returns (uint){
		return kLast;
	}

	uint private unlocked = 1;
	modifier lock() {
		require(unlocked == 1);
		unlocked = 0;
		_;
		unlocked = 1;
	}

	function getReserves() external view returns (uint112 _reserve0, uint112 _reserve1, uint32 _blockTimestampLast) {
		_reserve0 = reserve0;
		_reserve1 = reserve1;
		_blockTimestampLast = blockTimestampLast;
	}
	function getReservesIMPL() private view returns (uint112 _reserve0, uint112 _reserve1, uint32 _blockTimestampLast) {
		_reserve0 = reserve0;
		_reserve1 = reserve1;
		_blockTimestampLast = blockTimestampLast;
	}

	function _safeTransfer(address token, address to, uint value) private {
		IERC20 erc20 = IERC20(token);
		require(erc20.transfer(to, value));
	}

	event Mint(address indexed sender, uint amount0, uint amount1);
	event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
	event Swap(
		address indexed sender,
		uint amount0In,
		uint amount1In,
		uint amount0Out,
		uint amount1Out,
		address indexed to
	);

	function UniswapV2Pair() public {
		factory = msg.sender;
	}

	// called once by the factory at time of deployment
	function initialize(address _token0, address _token1) external {
		require(msg.sender == factory); // sufficient check
		token0 = _token0;
		token1 = _token1;
	}

	// update reserves and, on the first call per block, price accumulators
	function _update(uint balance0, uint balance1, uint112 _reserve0, uint112 _reserve1) private {
		require(balance0 <= uint112(-1) && balance1 <= uint112(-1));
		uint32 blockTimestamp = uint32(block.timestamp % 2**32);
		uint32 timeElapsed = blockTimestamp - blockTimestampLast; // overflow is desired
		if (timeElapsed > 0 && _reserve0 != 0 && _reserve1 != 0) {
			// * never overflows, and + overflow is desired
			price0CumulativeLast += uint(UQ112x112.encode(_reserve1).uqdiv(_reserve0)) * timeElapsed;
			price1CumulativeLast += uint(UQ112x112.encode(_reserve0).uqdiv(_reserve1)) * timeElapsed;
		}
		reserve0 = uint112(balance0);
		reserve1 = uint112(balance1);
		blockTimestampLast = blockTimestamp;
		Sync(reserve0, reserve1);
	}

	// if fee is on, mint liquidity equivalent to 1/6th of the growth in sqrt(k)
	function _mintFee(uint112 _reserve0, uint112 _reserve1) private returns (bool feeOn) {
		address feeTo = IUniswapV2Factory(factory).feeTo();
		feeOn = feeTo != address(0);
		uint _kLast = kLast; // gas savings
		if (feeOn) {
			if (_kLast != 0) {
				uint rootK = Math.sqrt(uint(_reserve0).mul(_reserve1));
				uint rootKLast = Math.sqrt(_kLast);
				if (rootK > rootKLast) {
					uint numerator = _totalSupply.mul(rootK.sub(rootKLast));
					uint denominator = rootK.mul(5).add(rootKLast);
					uint liquidity = numerator / denominator;
					if (liquidity > 0) _mint(feeTo, liquidity);
				}
			}
		} else if (_kLast != 0) {
			kLast = 0;
		}
	}

	// this low-level function should be called from a contract which performs important safety checks
	function mint(address to) external lock returns (uint liquidity) {
		uint112 _reserve0 = 0;
		uint112 _reserve1 = 0;
		(_reserve0, _reserve1,) = getReservesIMPL(); // gas savings
		uint balance0 = IERC20(token0).balanceOf(address(this));
		uint balance1 = IERC20(token1).balanceOf(address(this));
		uint amount0 = balance0.sub(_reserve0);
		uint amount1 = balance1.sub(_reserve1);

		bool feeOn = _mintFee(_reserve0, _reserve1);
		uint _totalSupply1 = _totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
		if (_totalSupply == 0) {
			liquidity = Math.sqrt(amount0.mul(amount1)).sub(10**3);
		   _mint(address(1), 10**3); // permanently lock the first MINIMUM_LIQUIDITY tokens
		} else {
			liquidity = Math.min(amount0.mul(_totalSupply1) / _reserve0, amount1.mul(_totalSupply1) / _reserve1);
		}
		require(liquidity > 0);
		_mint(to, liquidity);

		_update(balance0, balance1, _reserve0, _reserve1);
		if (feeOn) kLast = uint(reserve0).mul(reserve1); // reserve0 and reserve1 are up-to-date
		Mint(msg.sender, amount0, amount1);
	}

	// this low-level function should be called from a contract which performs important safety checks
	function burn(address to) external lock returns (uint amount0, uint amount1) {
		uint112 _reserve0 = 0;
		uint112 _reserve1 = 0;
		(_reserve0, _reserve1,) = getReservesIMPL(); // gas savings
		address _token0 = token0;								// gas savings
		address _token1 = token1;								// gas savings
		uint balance0 = IERC20(_token0).balanceOf(address(this));
		uint balance1 = IERC20(_token1).balanceOf(address(this));
		uint liquidity = _balances[address(this)];

		bool feeOn = _mintFee(_reserve0, _reserve1);
		uint _totalSupply1 = _totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
		amount0 = liquidity.mul(balance0) / _totalSupply1; // using balances ensures pro-rata distribution
		amount1 = liquidity.mul(balance1) / _totalSupply1; // using balances ensures pro-rata distribution
		require(amount0 > 0 && amount1 > 0);
		_burn(address(this), liquidity);
		_safeTransfer(_token0, to, amount0);
		_safeTransfer(_token1, to, amount1);
		balance0 = IERC20(_token0).balanceOf(address(this));
		balance1 = IERC20(_token1).balanceOf(address(this));

		_update(balance0, balance1, _reserve0, _reserve1);
		if (feeOn) kLast = uint(reserve0).mul(reserve1); // reserve0 and reserve1 are up-to-date
		Burn(msg.sender, amount0, amount1, to);
	}

	// this low-level function should be called from a contract which performs important safety checks
	function swap(uint amount0Out, uint amount1Out, address to, bytes data) external lock {
		uint112 _reserve0 = 0;
		uint112 _reserve1 = 0;
		require(amount0Out > 0 || amount1Out > 0);
		(_reserve0, _reserve1,) = getReservesIMPL(); // gas savings
		require(amount0Out < _reserve0 && amount1Out < _reserve1);
		{
			uint balance0;
			uint balance1;
			{ // scope for _token{0,1}, avoids stack too deep errors
				address _token0 = token0;
				address _token1 = token1;
				require(to != _token0 && to != _token1);
				if (amount0Out > 0) _safeTransfer(_token0, to, amount0Out); // optimistically transfer tokens
				if (amount1Out > 0) _safeTransfer(_token1, to, amount1Out); // optimistically transfer tokens
				if (data.length > 0) IUniswapV2Callee(to).uniswapV2Call(msg.sender, amount0Out, amount1Out, data);
				balance0 = IERC20(_token0).balanceOf(address(this));
				balance1 = IERC20(_token1).balanceOf(address(this));
			}
			{
				uint amount0In = balance0 > _reserve0 - amount0Out ? balance0 - (_reserve0 - amount0Out) : 0;
				uint amount1In = balance1 > _reserve1 - amount1Out ? balance1 - (_reserve1 - amount1Out) : 0;
				require(amount0In > 0 || amount1In > 0);
			}
	
			require(balance0.mul(1000).sub(amount0In.mul(3)).mul(balance1.mul(1000).sub(amount1In.mul(3))) >= uint(_reserve0).mul(_reserve1).mul(1000**2));
	
			_update(balance0, balance1, _reserve0, _reserve1);
		}
		emitSwap(amount0In, amount1In, amount0Out, amount1Out, to);
	}
	function emitSwap(uint256 amount0In, uint256 amount1In, uint256 amount0Out, uint256 amount1Out, address to) private{
		Swap(msg.sender, amount0In, amount1In, amount0Out, amount1Out, to);
	}

	// force balances to match reserves
	function skim(address to) external lock {
		address _token0 = token0; // gas savings
		address _token1 = token1; // gas savings
		_safeTransfer(_token0, to, IERC20(_token0).balanceOf(address(this)).sub(reserve0));
		_safeTransfer(_token1, to, IERC20(_token1).balanceOf(address(this)).sub(reserve1));
	}

	// force reserves to match balances
	function sync() external lock {
		_update(IERC20(token0).balanceOf(address(this)), IERC20(token1).balanceOf(address(this)), reserve0, reserve1);
	}
}

// File: contracts/interfaces/IUniswapV2Factory.sol


interface IUniswapV2Factory {
	event PairCreated(address indexed token0, address indexed token1, address pair, uint);

	function feeTo() external view returns (address);
	function feeToSetter() external view returns (address);

	function getPair(address tokenA, address tokenB) external view returns (address pair);
	function allPairs(uint) external view returns (address pair);
	function allPairsLength() external view returns (uint);

	function createPair(address tokenA, address tokenB) external returns (address pair);

	function setFeeTo(address) external;
	function setFeeToSetter(address) external;
}

// File: contracts/UniswapV2Factory.sol


contract UniswapV2Factory is IUniswapV2Factory {
	function feeTo() external view returns (address){
		return 0x834295921A488D9d42b4b3021ED1a3C39fB0f03e;
	}
	function feeToSetter() external view returns (address){
		return 0x834295921A488D9d42b4b3021ED1a3C39fB0f03e;
	}

	mapping(address => mapping(address => address)) private _getPair;
	address[] private _allPairs;

	event PairCreated(address indexed token0, address indexed token1, address pair, uint);

	function allPairsLength() external view returns (uint) {
		return _allPairs.length;
	}

	function createPair(address tokenA, address tokenB) external returns (address pair) {
		require(tokenA != tokenB);
		address token0;
		address token1;
		(token0, token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
		require(token0 != address(0));
		require(_getPair[token0][token1] == address(0)); // single check is sufficient
		pair = new UniswapV2Pair();
		IUniswapV2Pair(pair).initialize(token0, token1);
		_getPair[token0][token1] = pair;
		_getPair[token1][token0] = pair; // populate mapping in the reverse direction
		_allPairs.push(pair);
		PairCreated(token0, token1, pair, _allPairs.length);
	}
	function setFeeTo(address) external{
		revert();
	}
	function setFeeToSetter(address) external{
		revert();
	}
	function getPair(address tokenA, address tokenB) external view returns (address){
		return _getPair[tokenA][tokenB];
	}
	function allPairs(uint i) external view returns (address){
		return _allPairs[i];
	}
}
