# Instructive Red Black Trees
This library implements Red Black Trees, but where child nodes know if they are
the left child or the right child. This knowledge is then used to share code
between the symmetric cases in Red Black Trees.

# Space Considerations
Red black trees already "waste" some space for coloring nodes. Some additional
space for which branch of the parent node shouldn't be that impactful.

# Disclaimer
The library should be used to learn about Red Black Trees, not to learn Rust.
The library was written when the author is still somewhat new to Rust. Some of
the coding patterns may not reflect good Rust coding practices. The library is
not optimized in any way. The parent nodes are strong links, so they create
reference cycles leading to memory leaks.

The same key can be added multiple times in this version of Red Black Trees
without overriding old nodes. This might not be what you expect.
