//
// Created by juzix on 2021/6/4.
//

#include "polyVerifier.hpp"
#include <iostream>
using namespace std;

namespace hyrax_bls12_381 {
    polyVerifier::polyVerifier(polyProver &_p, const vector<G1> &_gens,int prover_commit_th) : p(_p), gens(_gens) {
        timer tmp_timer;
        tmp_timer.start();
        vt.start();
        cerr<<"hello!"<<endl;
        cerr<<prover_commit_th<<endl;
        comm_Z=p.commit(prover_commit_th);
        vt.stop();
        tmp_timer.stop();
        fprintf(stderr, "commit time: %.4f\n", tmp_timer.elapse_sec());
    }
    
    bool polyVerifier::verify(const vector<Fr> &_x, const Fr &RZL,int th) {
        fprintf(stderr, "Poly commit for 2^%d input.\n", (int) _x.size());
        timer tmp_timer0,tmp_timer1,tmp_timer2,tmp_timer3,tmp_timer4;
        tmp_timer0.start();
        vt.start();
        x = _x;
        split(lx, rx, x);tmp_timer0.stop();
        tmp_timer1.start();
        p.initBulletProve(lx, rx,th);
        tmp_timer1.stop();
        tmp_timer2.start();    
        auto R = expand(rx);
        assert(comm_Z.size() == R.size());
        tmp_timer2.stop();
        tmp_timer3.start();    
        G1::mulVec(comm_RZ, comm_Z.data(), R.data(), comm_Z.size());
        tmp_timer3.stop();
        tmp_timer4.start();    
        bool res = bulletVerify(gens, lx, comm_RZ, RZL);
        tmp_timer4.stop();
        cerr<<"poly verifier "<<tmp_timer0.elapse_sec()<<" "<<tmp_timer1.elapse_sec()<<" "<<tmp_timer2.elapse_sec()<<" "<<tmp_timer3.elapse_sec()<<" "<<tmp_timer4.elapse_sec()<<endl;
        vt.stop();
        return res;
    }

    bool polyVerifier::bulletVerify(vector<G1> g, vector<Fr> t, G1 comm,
                                    Fr y) {
        timer tmp_timer;
        tmp_timer.start();
        G1 lcomm, rcomm;
        Fr ly(0), ry(0);

        assert(checkPow2(g.size()));
        auto logn = t.size();
        while (true) {
            p.bulletProve(lcomm, rcomm, ly, ry);
            
            Fr randomness;
            randomness.setByCSPRNG();
            Fr irandomness;
            Fr::inv(irandomness, randomness);

            p.bulletUpdate(randomness);

            u64 hsize = g.size() >> 1;
            for (u64 i = 0; i < hsize; ++i)
                g[i] = g[i] * irandomness + g[i + hsize];
            g.resize(hsize);

            comm = lcomm * randomness + comm + rcomm * irandomness;
            cout<<"QX "<<y<<" "<<ly * (Fr::one() - t.back()) + ry * t.back()<<" ly:"<<ly<<" t.back"<<t.back()<<" ry "<<ry<<endl;
            if (y != ly * (Fr::one() - t.back()) + ry * t.back()) {
                fprintf(stderr, "y incorrect at %d.\n", (int) (logn - t.size()));
                return false;
            }
            y = ly * randomness + ry;

            if (t.size() == 1) {
                bool res = p.bulletOpen() == y && comm == g.back() * y;

                tmp_timer.stop();
                fprintf(stderr, "bulletProve time: %.4f\n", tmp_timer.elapse_sec());

                if (!res) {
                    fprintf(stderr, "last step incorrect.\n");
                    return false;
                }
                return true;
            }
            t.pop_back();
        }
    }
}