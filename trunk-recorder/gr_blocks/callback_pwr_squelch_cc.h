/* -*- c++ -*- */
/*
 * Power squelch block with callback support.
 *
 * Subclasses gr::analog::pwr_squelch_cc to add a callback that fires on
 * squelch state transitions, used to notify the Rust side without polling.
 *
 * gnuradio does not export the concrete pwr_squelch_cc_impl, so we subclass
 * the abstract interface and provide our own general_work().
 *
 * SPDX-License-Identifier: GPL-3.0-or-later
 */

#ifndef CALLBACK_PWR_SQUELCH_CC_H
#define CALLBACK_PWR_SQUELCH_CC_H

#include <functional>
#include <gnuradio/analog/pwr_squelch_cc.h>

class callback_pwr_squelch_cc : public gr::analog::pwr_squelch_cc
{
public:
    typedef std::shared_ptr<callback_pwr_squelch_cc> sptr;

    static sptr make(double db, double alpha = 0.0001, int ramp = 0, bool gate = false);

    virtual void set_squelch_callback(std::function<void(bool, double)> cb) = 0;
    virtual double get_pwr() = 0;
};

#endif /* CALLBACK_PWR_SQUELCH_CC_H */
