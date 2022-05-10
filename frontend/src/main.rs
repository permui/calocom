use std::fs;
use frontend::parser;

fn main() {
    let tmp = "./frontend/src/tmp.mag";
    let qsort = "../accept/qsort/qsort_calocom/qs.mag";
    let advisor = "../accept/advisor/advisor_calocom/advisor.mag";
    let mat = "../accept/matrix/mat_calocom/mat.mag"; 

    let tests = [tmp, qsort, advisor, mat];

    for p in tests {
        let s = fs::read_to_string(p).expect("read file fail");
        let m = parser::parse(&s);
        println!("{:#?}", m);
    }
}
