fn main() {
    let name = String::from("Rust");
    let say_hello = || format!("Hello, {}", name);

    println!("{:?}", say_hello()); // "Hello, Rust"

    let mut plain_rust = String::from("Rust");

    let mut awesome_rust = || plain_rust.push_str(" is awesome");
    awesome_rust();
    println!("{:?}", plain_rust) // "Rust is awesome"
}
