use rustpython_parser::{ast, parser};

pub mod interpreter;

pub fn parse_python_code(code: &str) -> Result<ast::Mod, String> {
    let parse_result = parser::parse(code, parser::Mode::Module, "<string>");
    match parse_result {
        Ok(module) => Ok(module),
        Err(err) => Err(format!("Parse error: {}", err)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn motivating_example() {
        let code = indoc::indoc! {r#"
            count = 0
            for line in order((lines := stdin.readlines()), by=lines.arrival_time):
                count += 1
                stdout.lines += f"{line} is line number {count}\n"
        "#};

        let result = parse_python_code(code);
        assert!(
            result.is_ok(),
            "Failed to parse basic Python code: {:?}",
            result
        );

        let ast = result.unwrap();
        println!("{:#?}", ast);
        match ast {
            ast::Mod::Module { body, .. } => {
                assert!(!body.is_empty(), "AST should not be empty");
                // Check that we have the expected number of statements
                assert_eq!(body.len(), 2, "Expected 2 statements, got {}", body.len());
            }
            _ => panic!("Expected module, got {:?}", ast),
        }
    }

    #[test]
    fn test_parse_basic_python() {
        let code = indoc::indoc! {r#"
            x = 42
            y = "hello"
            z = x + 10
            print(z)
        "#};

        let result = parse_python_code(code);
        assert!(
            result.is_ok(),
            "Failed to parse basic Python code: {:?}",
            result
        );

        let ast = result.unwrap();
        match ast {
            ast::Mod::Module { body, .. } => {
                assert!(!body.is_empty(), "AST should not be empty");
                // Check that we have the expected number of statements
                assert_eq!(body.len(), 4, "Expected 4 statements, got {}", body.len());
            }
            _ => panic!("Expected module, got {:?}", ast),
        }
    }

    #[test]
    fn test_parse_function_definition() {
        let code = indoc::indoc! {r#"
            def greet(name):
                return f"Hello, {name}!"

            result = greet("World")
        "#};

        let result = parse_python_code(code);
        assert!(
            result.is_ok(),
            "Failed to parse function definition: {:?}",
            result
        );

        let ast = result.unwrap();
        match ast {
            ast::Mod::Module { body, .. } => {
                assert_eq!(body.len(), 2, "Expected 2 statements, got {}", body.len());
            }
            _ => panic!("Expected module, got {:?}", ast),
        }
    }

    #[test]
    fn test_parse_conditional_statement() {
        let code = indoc::indoc! {r#"
            if x > 0:
                print("positive")
            elif x < 0:
                print("negative")
            else:
                print("zero")
        "#};

        let result = parse_python_code(code);
        assert!(
            result.is_ok(),
            "Failed to parse conditional statement: {:?}",
            result
        );

        let ast = result.unwrap();
        match ast {
            ast::Mod::Module { body, .. } => {
                assert_eq!(body.len(), 1, "Expected 1 statement, got {}", body.len());
            }
            _ => panic!("Expected module, got {:?}", ast),
        }
    }

    #[test]
    fn test_parse_invalid_syntax() {
        let code = "def invalid syntax here";

        let result = parse_python_code(code);
        assert!(result.is_err(), "Should fail to parse invalid syntax");
    }
}
