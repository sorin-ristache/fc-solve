"use strict";

if (typeof define !== 'function') {
    var define = require('amdefine')(module);
}

define(["web-fc-solve", "libfreecell-solver.min", 'dist/fc_solve_find_index_s2ints'], function (w, Module, s2i) {

    var FC_Solve_init_wrappers_with_module = w.FC_Solve_init_wrappers_with_module;
    var _my_module = Module()({});
    var deal_ms_fc_board = w.deal_ms_fc_board;
    FC_Solve_init_wrappers_with_module(_my_module);

var entityMap = {
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    '"': '&quot;',
    "'": '&#39;',
    "/": '&#x2F;'
};

function escapeHtml(string) {
    return String(string).replace(/[&<>"'\/]/g, function (s) {
        return entityMap[s];
    });
}

// Thanks to Stefan Petrea ( http://garage-coding.com/ ) for inspiring this
// feature.
var previous_deal_idx = 1;

function populate_input_with_numbered_deal() {

    var input_s = $('#deal_number').val();
    /*
    var new_idx = prompt("Enter MS Freecell deal number:");

    // Prompt returned null (user cancelled).
    if (! new_idx) {
        return;
    }

    previous_deal_idx = parseInt(new_idx);
    */

    if (! input_s.match(/^[1-9][0-9]*$/)) {
        alert("Wrong input - please enter a positive integer.");
        return;
    }

    previous_deal_idx = parseInt(input_s);

    $("#stdin").val(
        "# MS Freecell Deal #" + previous_deal_idx +
        "\n#\n" +
        deal_ms_fc_board(previous_deal_idx)
    );

    return;
}

class FC_Solve_Bookmarking {
    constructor(args) {
        var that = this;

        that.bookmark_controls = args.bookmark_controls;
        that.show = args.show;

        return;
    }
    _get_loc() {
        return window.location;
    }
    _get_base_url() {
        var that = this;

        var loc = that._get_loc();
        return loc.protocol + '//' + loc.host + loc.pathname;
    }
    _each_control(cb) {
        var that = this;

        that.bookmark_controls.forEach(cb);
    }
    on_bookmarking() {
        var that = this;

        var get_v = function(myid) {
            var ctl = $('#' + myid);
            return ctl.is(':checkbox') ?  (ctl.is(':checked') ? '1' : '0') : ctl.val();
        };

        var control_values = {};

        that._each_control(function (myid) {
            control_values[myid] = get_v(myid);
        });

        var bookmark_string = that._get_base_url() + '?' + $.querystring(control_values);

        $("#fcs_bm_results_input").val(bookmark_string);

        var a_elem = $("#fcs_bm_results_a");
        // Too long to be effective.
        // a_elem.text(bookmark_string);
        a_elem.attr('href', bookmark_string);

        $("#fcs_bookmark_wrapper").removeClass("disabled");

        return;
    }
    restore_bookmark() {
        var that = this;

        var qs = that._get_loc().search;

        if (! qs.length) {
            return;
        }

        // Remove trailing 1.
        var params = $.querystring(qs.substr(1));

        that._each_control(function (myid) {
            var ctl = $('#' + myid);
            if (ctl.is(':checkbox')) {
                ctl.prop('checked', ((params[myid] == "1") ? true : false));
            }
            else {
                ctl.val(params[myid]);
            }
        });

        that.show.forEach(function (rec) {
            var id = rec.id;
            var deps = rec.deps;

            var should_toggle = false;
            deps.forEach(function (d) {
                if ($("#" + d).val().length > 0) {
                    should_toggle = true;
                }
            });

            if (should_toggle) {
                if ($("#" + id).hasClass("disabled")) {
                    rec.callback();
                }
            }
        });

        return;
    }
}

function toggle_advanced() {
    var ctl = $("#fcs_advanced");
    ctl.toggleClass("disabled");

    var set_text = function (my_text) {
        $("#fcs_advanced_toggle").text(my_text);
    };

    set_text(
        ctl.hasClass("disabled") ? "Advanced ▼" : "Advanced ▲"
    );

    return;
}

function _create_bmark_obj() {
    return new FC_Solve_Bookmarking({ bookmark_controls: ['stdin', 'deal_number',], show: [],});
}

function on_bookmarking() {
    return _create_bmark_obj().on_bookmarking();
}

function restore_bookmark() {
    return _create_bmark_obj().restore_bookmark();
}
    // Taken from https://stackoverflow.com/questions/2901102/how-to-print-a-number-with-commas-as-thousands-separators-in-javascript
    // thanks.
    const numberWithCommas = (x) => {
        return x.toString().replace(/\B(?=(\d{3})+(?!\d))/g, ",");
    };

    function find_deal_ui() {
        const deal_str = $("#stdin").val().replace(/#[^\r\n]*\r?\n?/g, '').replace(/\r+\n/, "\n").replace(/([^\n])$/, "$1\n");
        const ints = s2i.find_index__board_string_to_ints(deal_str);
        const ints_s = ints.map((i) => { let ret = i.toString(); return " ".repeat(10-ret.length) + ret; }).join('');
        let df = new w.Freecell_Deal_Finder({});
        df.fill(ints_s);
        let ctl = $("#fc_solve_status");
        df.run(1, '8589934591',
            (args) => {
                ctl.html(escapeHtml("Reached No. " + numberWithCommas(args.start)));
                return;
            }
        );

        function resume() {
            const ret_Deal = df.cont();
            if (ret_Deal.found) {
                ctl.html("Found " + ret_Deal.result.toString());
            } else if (ret_Deal.cont) {
                setTimeout(() => { resume(); }, 1);
            } else {
                ctl.html("No such deal");
            }
        }

        resume();
    }

function set_up_handlers() {
    $("#populate_input").click(populate_input_with_numbered_deal);
    $("#run_do_solve").click(find_deal_ui);
    $("#fc_solve_bookmark_button").click(on_bookmarking);
}

function set_up() {
    restore_bookmark();
    set_up_handlers();
}

    return { find_deal_ui: find_deal_ui, set_up: set_up, set_up_handlers: set_up_handlers};
});
