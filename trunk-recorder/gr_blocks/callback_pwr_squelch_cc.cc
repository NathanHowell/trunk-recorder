/* -*- c++ -*- */
/*
 * Power squelch block with callback support.
 *
 * SPDX-License-Identifier: GPL-3.0-or-later
 */

#include "./callback_pwr_squelch_cc.h"
#include <gnuradio/filter/single_pole_iir.h>
#include <gnuradio/io_signature.h>
#include <gnuradio/math.h>

namespace {

class callback_pwr_squelch_cc_impl : public callback_pwr_squelch_cc
{
private:
    // Power measurement
    double d_threshold;
    double d_pwr;
    gr::filter::single_pole_iir<double, double, double> d_iir;

    // Squelch state machine
    int d_ramp;
    int d_ramped;
    bool d_gate;
    double d_envelope;
    enum { ST_MUTED, ST_ATTACK, ST_UNMUTED, ST_DECAY } d_state;

    // Tags and messages
    const pmt::pmt_t d_sob_key;
    const pmt::pmt_t d_eob_key;
    const pmt::pmt_t d_squelch_state_port;
    const pmt::pmt_t d_muted_key;
    const pmt::pmt_t d_pwr_db_key;
    bool d_tag_next_unmuted;

    // Callback
    std::function<void(bool, double)> d_squelch_cb;

    double get_pwr_db() const { return 10.0 * std::log10(d_pwr); }

    void publish_state(bool muted, double pwr_db)
    {
        if (d_squelch_cb)
            d_squelch_cb(muted, pwr_db);

        pmt::pmt_t msg = pmt::make_dict();
        msg = pmt::dict_add(msg, d_muted_key, muted ? pmt::PMT_T : pmt::PMT_F);
        msg = pmt::dict_add(msg, d_pwr_db_key, pmt::from_double(pwr_db));
        message_port_pub(d_squelch_state_port, msg);
    }

protected:
    // Pure virtuals inherited from pwr_squelch_cc / squelch_base_cc.
    // Not called by our general_work() but required to make the class concrete.
    void update_state(const gr_complex&) override {}
    bool mute() const override { return d_pwr < d_threshold; }

public:
    callback_pwr_squelch_cc_impl(double db, double alpha, int ramp, bool gate)
        : gr::block("callback_pwr_squelch_cc",
                     gr::io_signature::make(1, 1, sizeof(gr_complex)),
                     gr::io_signature::make(1, 1, sizeof(gr_complex))),
          d_pwr(0),
          d_iir(alpha),
          d_ramp(ramp),
          d_ramped(0),
          d_gate(gate),
          d_envelope(ramp ? 0.0 : 1.0),
          d_state(ST_MUTED),
          d_sob_key(pmt::intern("squelch_sob")),
          d_eob_key(pmt::intern("squelch_eob")),
          d_squelch_state_port(pmt::intern("squelch_state")),
          d_muted_key(pmt::intern("muted")),
          d_pwr_db_key(pmt::intern("pwr_db")),
          d_tag_next_unmuted(true)
    {
        d_threshold = std::pow(10.0, db / 10.0);
        message_port_register_out(d_squelch_state_port);
    }

    ~callback_pwr_squelch_cc_impl() override = default;

    // --- callback_pwr_squelch_cc interface ---

    void set_squelch_callback(std::function<void(bool, double)> cb) override
    {
        gr::thread::scoped_lock l(d_setlock);
        d_squelch_cb = std::move(cb);
    }

    double get_pwr() override { return get_pwr_db(); }

    // --- pwr_squelch_cc interface ---

    std::vector<float> squelch_range() const override
    {
        return { -50.0f, +50.0f, 1.0f };
    }

    double threshold() const override { return 10.0 * std::log10(d_threshold); }

    void set_threshold(double db) override
    {
        gr::thread::scoped_lock l(d_setlock);
        d_threshold = std::pow(10.0, db / 10.0);
    }

    void set_alpha(double alpha) override
    {
        gr::thread::scoped_lock l(d_setlock);
        d_iir.set_taps(alpha);
    }

    // --- squelch_base_cc interface ---

    int ramp() const override { return d_ramp; }

    void set_ramp(int ramp) override
    {
        gr::thread::scoped_lock l(d_setlock);
        d_ramp = ramp;
    }

    bool gate() const override { return d_gate; }

    void set_gate(bool gate) override
    {
        gr::thread::scoped_lock l(d_setlock);
        d_gate = gate;
    }

    bool unmuted() const override
    {
        return d_state == ST_UNMUTED || d_state == ST_ATTACK;
    }

    // --- gr::block ---

    int general_work(int noutput_items,
                     gr_vector_int& ninput_items,
                     gr_vector_const_void_star& input_items,
                     gr_vector_void_star& output_items) override
    {
        const auto* in = static_cast<const gr_complex*>(input_items[0]);
        auto* out = static_cast<gr_complex*>(output_items[0]);

        int j = 0;
        gr::thread::scoped_lock l(d_setlock);

        for (int i = 0; i < noutput_items; i++) {
            // Update power estimate
            d_pwr = d_iir.filter(in[i].real() * in[i].real() +
                                 in[i].imag() * in[i].imag());

            switch (d_state) {
            case ST_MUTED:
                if (!mute()) {
                    d_state = d_ramp ? ST_ATTACK : ST_UNMUTED;
                    if (d_state == ST_UNMUTED)
                        d_tag_next_unmuted = true;
                }
                break;

            case ST_UNMUTED:
                if (d_tag_next_unmuted) {
                    d_tag_next_unmuted = false;
                    add_item_tag(0, nitems_written(0) + j, d_sob_key, pmt::PMT_NIL);
                    publish_state(false, get_pwr_db());
                }
                if (mute()) {
                    d_state = d_ramp ? ST_DECAY : ST_MUTED;
                    if (d_state == ST_MUTED) {
                        add_item_tag(0, nitems_written(0) + j, d_eob_key, pmt::PMT_NIL);
                        publish_state(true, get_pwr_db());
                    }
                }
                break;

            case ST_ATTACK:
                d_envelope = 0.5 - std::cos(GR_M_PI * (++d_ramped) / d_ramp) / 2.0;
                if (d_ramped >= d_ramp) {
                    d_state = ST_UNMUTED;
                    d_tag_next_unmuted = true;
                    d_envelope = 1.0;
                }
                break;

            case ST_DECAY:
                d_envelope = 0.5 - std::cos(GR_M_PI * (--d_ramped) / d_ramp) / 2.0;
                if (d_ramped == 0) {
                    d_state = ST_MUTED;
                    add_item_tag(0, nitems_written(0) + j, d_eob_key, pmt::PMT_NIL);
                    publish_state(true, get_pwr_db());
                }
                break;
            }

            if (d_state != ST_MUTED) {
                out[j++] = in[i] * gr_complex(d_envelope, 0.0);
            } else if (!d_gate) {
                out[j++] = 0.0;
            }
        }

        consume_each(noutput_items);
        return j;
    }
};

} // anonymous namespace

callback_pwr_squelch_cc::sptr
callback_pwr_squelch_cc::make(double db, double alpha, int ramp, bool gate)
{
    return gnuradio::make_block_sptr<callback_pwr_squelch_cc_impl>(db, alpha, ramp, gate);
}
