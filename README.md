# CountMap

[![Travis Build Status](https://travis-ci.org/vbrandl/countmap.svg?branch=master)](https://travis-ci.org/vbrandl/countmap)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](https://github.com/vbrandl/countmap/blob/master/LICENSE-MIT)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](https://github.com/vbrandl/countmap/blob/master/LICENSE-APACHE)
[![crates.io](https://meritbadge.herokuapp.com/countmap)](https://crates.io/crates/countmap)

Implementation of a count map in Rust. A map that holds a counter as a
value, that gets incremented each time the key is added to the map.
This implementation simply decorates the HashMap from the Rust std
library.

[Documentation](https://docs.rs/countmap)

## Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
countmap = "0.1"
```

Next, add this to your crate root:

```rust
extern crate countmap;
```

Now you can use a count map in your code:

```rust
fn main() {
	let map = countmap::CountMap::new();
	map.insert_or_increment("foo");
}
```
