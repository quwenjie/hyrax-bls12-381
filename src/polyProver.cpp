//
// Created by juzix on 2021/6/4.
//

#include "polyProver.hpp"
#include <mcl/bls12_381.hpp>
#include <iostream>
using namespace std;

#define G1_SIZE (Fp::getByteSize())
#define Fr_SIZE (Fr::getByteSize())

using std::vector;
namespace hyrax_bls12_381 {
    void MUL_VEC(G1& ret,G1* vec1,int* vec2,int n)
    {
        
        G1 tmp1,tmp2;
        G1 tmp_1,tmp_2;
        tmp_1.clear();
        tmp_2.clear();
        for(int i=0;i<n;i++)
        {
            int a=vec2[i]/16;
            int b=vec2[i]&15;
            assert(vec2[i]==16*a+b);
            G1::mulSmallInt(tmp1,vec1[i],a,false);
            tmp_1+=tmp1;//vec1[i]*a;
            G1::mulSmallInt(tmp2,vec1[i],b,false);
            tmp_2+=tmp2;//vec1[i]*b;
        }
        ret=tmp_1*16+tmp_2;
    }
    void MUL_VEC_bucket(G1& ret,G1* vec1,int* vec2,int n)
    {
        G1 tmp1,tmp2;
        G1 tmp_1,tmp_2;
        G1 W[16];
        for(int i=0;i<16;i++)
            W[i].clear();

        for(int i=0;i<n;i++)
        {
            assert(vec2[i]<=255 && vec2[i]>=0);
            for(int j=0;j<8;j++)
            {
                if(vec2[i]&(1<<j))
                    W[j]+=vec1[i];    
            }
        }
        for(int j=0;j<8;j++)
        {
            ret=ret+W[j]*(1<<j);
        }
    }


    polyProver::polyProver(const vector<int> &_Zi, const vector<G1> &_gens) :
            Zi(_Zi),gens(_gens) 
    {
        bit_length = myLog2(_Zi.size());
        ps = 0;
    }
    polyProver::polyProver(const vector<Fr> &_Z, const vector<G1> &_gens) :
            Z(_Z), gens(_gens) {
        bit_length = myLog2(_Z.size());
        ps = 0;
    }
    /*vector<G1> polyProver::commit() {
        pt.start();
        u8 r_bit_length = bit_length >> 1;
        u8 l_bit_length = bit_length - r_bit_length;

        u64 rsize = 1ULL << r_bit_length, lsize = 1ULL << l_bit_length;
        assert(lsize == gens.size());

        comm_Z.resize(rsize);
        for (u64 i = 0; i < rsize; ++i)
            G1::mulVec(comm_Z[i], gens.data(), Z.data() + i * lsize, lsize);

        pt.stop();
        ps += G1_SIZE * comm_Z.size();
        return comm_Z;
    }
    */
    vector<G1> polyProver::commit() 
    {
        timer tmp_timer;
        
        u8 r_bit_length = bit_length >> 1;
        u8 l_bit_length = bit_length - r_bit_length;

        u64 rsize = 1ULL << r_bit_length, lsize = 1ULL << l_bit_length;
        assert(lsize == gens.size());

        timer tmp_timer2;
        comm_Z.resize(rsize);
        tmp_timer2.start();
        if(Z.size())
        {
            for (u64 i = 0; i < rsize; ++i)
                G1::mulVec(comm_Z[i], gens.data(), Z.data() + i * lsize, lsize);
        }
        else
        {
            for (u64 i = 0; i < rsize; ++i)
            {
                MUL_VEC_bucket(comm_Z[i], gens.data(), Zi.data() + i * lsize, lsize);
            }
        }
        
        tmp_timer2.stop();
        cerr<<"ours: "<<tmp_timer2.elapse_sec()<<endl;
        ps += G1_SIZE * comm_Z.size();
        return comm_Z;
    }

    Fr polyProver::evaluate(const vector<Fr> &x) 
    {
        timer tmp_timer1,tmp_timer2;
        tmp_timer1.start();
        auto X = expand(x);
        tmp_timer1.stop();
        tmp_timer2.start();
        Fr res;
        if(Z.size())
        {
            for (u64 i = 0; i < X.size(); ++i) 
                res = !i ? Z[i] * X[i] : res + Z[i] * X[i];
        }
        else
        {
            for (u64 i = 0; i < X.size(); ++i) 
                res = !i ? Zi[i] * X[i] : res + Zi[i] * X[i];
        }
        tmp_timer2.stop();
        cerr<<"prover evaluate time: "<<tmp_timer1.elapse_sec()<<" "<<tmp_timer2.elapse_sec()<<endl;
        return res;
    }

    double polyProver::getPT() const {
        return pt.elapse_sec();
    }

    double polyProver::getPS() const {      // KB
        return ps / 1024.0;
    }

    void polyProver::initBulletProve(const vector<Fr> &_lx, const vector<Fr> &_rx) {
        Fr zero;
        zero.clear();
        pt.start();

        t = _lx;
        L = expand(_lx);
        R = expand(_rx);

        u64 lsize_ex = L.size(), rsize_ex = R.size();
        //assert(lsize_ex * rsize_ex == Z.size());
        assert(lsize_ex == gens.size());

        RZ.resize(lsize_ex, zero);
        if(Z.size())
        {
            for (u64 j = 0; j < rsize_ex; ++j)
                for (u64 i = 0; i < lsize_ex; ++i)
                    RZ[i] = !j ? R[j] * Z[j * lsize_ex + i] : RZ[i] + R[j] * Z[j * lsize_ex + i];
        }
        else
        {
            for (u64 j = 0; j < rsize_ex; ++j)
                for (u64 i = 0; i < lsize_ex; ++i)
                    RZ[i] = !j ? R[j] * Zi[j * lsize_ex + i] : RZ[i] + R[j] * Zi[j * lsize_ex + i];
        }
        bullet_g = gens;
        bullet_a = RZ;
        scale = Fr::one();
        pt.stop();
    }

    void polyProver::bulletProve(G1 &lcomm, G1 &rcomm, Fr &ly, Fr &ry) {
        pt.start();
        assert(!(bullet_a.size() & 1));
        u64 hsize = bullet_a.size() >> 1;

        G1::mulVec(lcomm, bullet_g.data(), bullet_a.data(), hsize);
        G1::mulVec(rcomm, bullet_g.data() + hsize, bullet_a.data() + hsize, hsize);

        Fr tmp;
        Fr::inv(tmp, Fr::one() - t.back());
        scale *= tmp;

        for (int i = 0; i < hsize; ++i) {
            ly = !i ? bullet_a[i] * L[i] : ly + bullet_a[i] * L[i];
            ry = !i ? bullet_a[i + hsize] * L[i] : ry + bullet_a[i + hsize] * L[i];
        }
        ly *= scale;
        ry *= scale;
        pt.stop();
        ps += (G1_SIZE + Fr_SIZE) * 2;
    }

    void polyProver::bulletUpdate(const Fr &randomness) {
        pt.start();
        Fr irandomness;
        Fr::inv(irandomness, randomness);
        u64 hsize = bullet_a.size() >> 1;
        for (u64 i = 0; i < hsize; ++i) bullet_a[i] = bullet_a[i] * randomness + bullet_a[i + hsize];
        for (u64 i = 0; i < hsize; ++i) bullet_g[i] = bullet_g[i] * irandomness + bullet_g[i + hsize];
        bullet_a.resize(hsize);
        bullet_g.resize(hsize);
        t.pop_back();
        pt.stop();
    }

    Fr polyProver::bulletOpen() {
        assert(bullet_a.size() == 1);

        ps += Fr_SIZE;
        return bullet_a.back();
    }

    const vector<G1> &polyProver::getGens() const {
        return gens;
    }
}