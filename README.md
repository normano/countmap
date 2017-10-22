# CountMap

[![Travis Build Status](https://travis-ci.org/vbrandl/countmap.svg?branch=master)](https://travis-ci.org/vbrandl/countmap)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](https://github.com/vbrandl/countmap/blob/master/LICENSE-MIT)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](https://github.com/vbrandl/countmap/blob/master/LICENSE-APACHE)
[![crates.io](https://meritbadge.herokuapp.com/countmap)](https://crates.io/crates/countmap)

Implementation of a count map in Rust. A map that holds a counter as a
value, that gets incremented each time the key is added to the map.
This implementation simply decorates the HashMap from the Rust std
library. To provide a generic counter (any number type should work)
some traits from the `num-traits` crate are used.

[Documentation](https://docs.rs/countmap)

## Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
countmap = "0.2"
```

Next, add this to your crate root:

```rust
extern crate countmap;
```

Now you can use a count map in your code:

```rust
extern crate countmap;
use countmap::CountMap;

fn main() {
	let map: CountMap<_, u16> = CountMap::new();
	map.insert_or_increment("foo");
	map.insert_or_increment("foo");
	map.insert_or_increment("foo");
	assert_eq!(map.get_count(&"foo"), Some(3));
}
```

## License

Countmap is licensed under either of the following, at your option:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
http://www.apache.org/licenses/LICENSE-2.0)
  * MIT License ([LICENSE-MIT](LICENSE-MIT) or
http://opensource.org/licenses/MIT)

