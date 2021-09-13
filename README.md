# hyrax-bls12-381
This is a polynomial commitment implementation refer to [Hyrax](https://eprint.iacr.org/2017/1132.pdf) based on BLS12-381 implemented by [mcl](https://github.com/herumi/mcl). The underline operations of scalar and group element refers to OpenSSL.
This scheme is particularly for multi-linear extension of an array.

Here is a simple example to use it:
``` C++
#include "typedef.hpp"
#include "Fr.hpp"
#include "polyProver.hpp"
#include "polyVerifier.hpp"
#include <bits/stdc++.h>

using std::vector;
using std::string;

#define LOGN_ID 0
#define PT_ID 1
#define VT_ID 2
#define PS_ID 3

vector<string> ans(4);

template <typename T>
string to_string_wp(const T a_value, const int n = 4) {
    std::ostringstream out;
    out.precision(n);
    out << std::fixed << a_value;
    return out.str();
}

int main(int argc, char *argv[]) {
    u8 logn = atoi(argv[1]);

    u64 n = 1ULL << logn;
    u64 n_sqrt = 1ULL << (logn - (logn >> 1));
    vector<F> poly_coeff(n);
    vector<Ec> gens(n_sqrt);
    vector<F> r(logn);

    for (u64 i = 0; i < n; ++i) poly_coeff[i].setByCSPRNG();
    for (u64 i = 0; i < n_sqrt; ++i) {
        Fr tmp;
        tmp.setByCSPRNG();
        gens[i] = mcl::bn::getG1basePoint() * tmp;
    }
    for (u8 i = 0; i < logn; ++i) r[i].setByCSPRNG();
    hyrax_bls12_381::polyProver p(poly_coeff, gens);
    hyrax_bls12_381::polyVerifier v(p, gens);
    v.verify(r, p.evaluate(r));

    ans[LOGN_ID] = std::to_string(logn);
    ans[PT_ID] = to_string_wp(p.getPT());   // prover time
    ans[VT_ID] = to_string_wp(v.getVT());   // verifier time
    ans[PS_ID] = to_string_wp(p.getPS());   // proof size

    for (int i = 0; i < ans.size(); ++i)
        printf("%s, ", ans[i].c_str());
    puts("");
    return 0;
}
```
