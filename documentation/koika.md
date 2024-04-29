# Koika

## Rules

* Rules are used instead of synchronous "always" blocks.
* Unlike "always" blocks rules are not run concurrently but using One Rule At A Time (ORAAT) semantics.
* All rules are executed sequentially but in the same clock cycle to create an illusion that they are being executed concurrently.
* Executing the rules one at a time avoids race conditions where multiple blocks are writing to the same register.
* The order of execution for rules depends on the scheduler.
* A rule whose execuion would violate the ORAAT semantics is aborted dynamically.

* All rules are of type ``` rule_name_t``` 

```
Inductive rule_name_t :=
    | inc_r
    | check_r. 
```



## External Functions

* External functions are used to access the external IPs.
* All external functions need to be defined in ```ext_fn_t```

``` 
Inductive ext_fn_t :=
    | ext_reset.
```

* The inputs and output types of the external function have to be defined.
* If no external functions are present empty_ext_fn_t needs to be defined in above inductive data type.

## Functions

```
Definition inc: UInternalFunction reg_t ext_fn_t :=
{{ fun inc (value: bits_t 3) : bits_t 3 =>
value + |3`d1|
}}.
```