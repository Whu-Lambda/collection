struct UserModel {
    is_active: bool,
    username: String,
    email: String,
}

#[cfg(test)]
mod tests {
    use self::super::*;

    #[test]
    fn test_user() {
        let user1 = UserModel {
            email: String::from("someone@example.com"),
            username: String::from("rust"),
            is_active: true,
        };

        println!("{:?}", user1);
    }
}
