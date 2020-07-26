use clap::{App, AppSettings, Arg, ArgGroup, ArgMatches, SubCommand};
use std::{
    cmp::Ordering,
    convert::{Into, TryFrom},
    ops::{Add, Sub},
    str::FromStr,
};

macro_rules! md {
    ($e:expr, $n:expr) => {
        (($e % $n) + $n) % $n
    };
}

const LENGTHS: [i16; 4] = [1000, 60, 60, 24];

#[derive(Debug, PartialEq, Eq, Clone)]
struct TimeStamp([i16; 4]);

impl TimeStamp {
    fn new(p: [i16; 4]) -> Self {
        // validate the data in the parameter array
        let mut encoded_ts = p.clone();
        let mut carry = 0;
        for i in 0..4 {
            let ridx = 3 - i;
            encoded_ts[i] = md!(p[ridx] + carry, LENGTHS[i]);
            carry = p[ridx] / LENGTHS[i];
        }
        TimeStamp(encoded_ts)
    }
}

impl PartialOrd for TimeStamp {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TimeStamp {
    fn cmp(&self, other: &Self) -> Ordering {
        // a timestamp is bigger if the distance
        for i in 0..4 {
            // starting from the biggest time unit (hr.) then moving backwards towards the
            // millisecond range.
            let ridx = 3 - i;
            if self.0[ridx] < other.0[ridx] {
                return Ordering::Less;
            }

            if self.0[ridx] > other.0[ridx] {
                return Ordering::Greater;
            }
        }

        Ordering::Equal
    }
}

impl TryFrom<Box<[i16]>> for TimeStamp {
    type Error = Box<[i16]>;

    fn try_from(v: Box<[i16]>) -> Result<Self, Self::Error> {
        // check that the box is big enough.
        let big_enough_box = <Box<[_; 4]>>::try_from(v)?;
        Ok(TimeStamp::new(*big_enough_box))
    }
}

impl FromStr for TimeStamp {
    type Err = Box<[i16]>;

    fn from_str(raw_timestamp: &str) -> Result<Self, Self::Err> {
        // parse it, at this point we still don't know if the timestamp is well formed.
        let prob_ill_formed = raw_timestamp
            .split(':')
            .flat_map(|s| s.split(','))
            .filter_map(|s| s.parse::<i16>().ok())
            .collect::<Box<[_]>>();

        // verify that it is indeed well formed.
        Ok(TimeStamp::try_from(prob_ill_formed)?)
    }
}

impl Sub for TimeStamp {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        // array of cycle lengths for each position.
        // the actual algorithm
        let mut result: [i16; 4] = [0; 4];
        let mut carry = 0;
        for i in 0..4 {
            // compute the proxy for modulus req.
            let proxy = self.0[i] - other.0[i];
            match i {
                3 => result[i] = proxy - carry,
                _ => {
                    // if proxy is zero then we keep the position as zero.
                    // otherwise we would need to use max on >= 0 case.
                    if proxy < 0 {
                        result[i] = md!(proxy, LENGTHS[i]) - carry;
                        carry = 1;
                    } else if proxy > 0 {
                        result[i] = (proxy % LENGTHS[i]) - carry;
                        carry = 0;
                    }
                }
            }
        }

        TimeStamp(result)
    }
}

impl Add for TimeStamp {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        //
        let mut result: [i16; 4] = [0; 4];
        let mut carry = 0;
        for i in 0..4 {
            // compute the proxy for modulus req.
            let proxy = self.0[i] + other.0[i];
            match i {
                3 => result[i] = proxy + carry,
                _ => {
                    result[i] = md!(proxy, LENGTHS[i]) + carry;
                    carry = proxy / LENGTHS[i];
                }
            }
        }

        TimeStamp(result)
    }
}

impl Into<String> for TimeStamp {
    fn into(self) -> String {
        // "00:00:00,000"
        let hr = format!("{:0>2}:", self.0[3]);
        let m = format!("{:0>2}:", self.0[2]);
        let s = format!("{:0>2},", self.0[1]);
        let ms = format!("{:0>3}", self.0[0]);
        [hr, m, s, ms].concat()
    }
}

fn build_raw_timestamp<'a>(matches: &'a ArgMatches) -> Option<String> {
    // start with smallest unit, and check for carry over.
    let ms = matches.value_of("milliseconds").unwrap_or("000");
    let s = matches.value_of("seconds").unwrap_or("00");
    let m = matches.value_of("minutes").unwrap_or("00");
    let h = matches.value_of("hours").unwrap_or("00");

    Some([h, ":", m, ":", s, ",", ms].concat())
}

fn run(matches: &ArgMatches) -> Option<TimeStamp> {
    let start = matches.value_of("start")?;
    let start = TimeStamp::from_str(start).ok()?;

    match matches.subcommand() {
        ("add", Some(add_m)) => {
            if add_m.is_present("quick") {
                let end = build_raw_timestamp(add_m)?;
                let end = TimeStamp::from_str(&end).ok()?;
                Some(end + start)
            } else {
                let end = TimeStamp::from_str(add_m.value_of("formatted").unwrap()).ok()?;
                Some(end + start)
            }
        }
        ("sub", Some(sub_m)) => {
            // TODO: verify that the `end` timestamp is bigger than `start`.
            if sub_m.is_present("quick") {
                let end = build_raw_timestamp(sub_m)?;
                let end = TimeStamp::from_str(&end).ok()?;
                let max = std::cmp::max(end.clone(), start.clone());
                let min = std::cmp::min(end, start);
                Some(max - min)
            } else {
                let end = TimeStamp::from_str(sub_m.value_of("formatted").unwrap()).ok()?;
                let max = std::cmp::max(end.clone(), start.clone());
                let min = std::cmp::min(end, start);
                Some(max - min)
            }
        }
        _ => unreachable!(),
    }
}

fn main() {
    let fmtarg = Arg::with_name("formatted")
        .short("f")
        .help("provide a formatted timestamp, e.g. \"hh:mm:ss,ms\"")
        .required_unless("quick")
        .takes_value(true);

    let quickarg = Arg::with_name("quick")
        .short("q")
        .help("provide a quick-timestamp, useful when only using a single unit (hrs, mins, etc.)");

    let hours = Arg::with_name("hours").long("hrs").takes_value(true);
    let minutes = Arg::with_name("minutes").short("m").takes_value(true);
    let seconds = Arg::with_name("seconds").short("s").takes_value(true);
    let msecs = Arg::with_name("milliseconds")
        .long("msecs")
        .takes_value(true);

    let quick_ts_group = ArgGroup::with_name("quick-timestamp")
        .args(&["hours", "minutes", "seconds", "milliseconds"])
        .multiple(true)
        .requires("quick");

    let dataformat = ArgGroup::with_name("data-format").args(&["quick", "formatted"]);

    let add = SubCommand::with_name("add")
        .about("add another timestamp")
        .args(&[
            fmtarg.clone(),
            quickarg.clone(),
            hours.clone(),
            minutes.clone(),
            seconds.clone(),
            msecs.clone(),
        ])
        .groups(&[quick_ts_group.clone(), dataformat.clone()]);

    let sub = SubCommand::with_name("sub")
        .about("subtract an equal or lower timestamp")
        .args(&[fmtarg, quickarg, hours, minutes, seconds, msecs])
        .groups(&[quick_ts_group, dataformat]);

    let matches = App::new("edmeti")
        .author("snOm3ad")
        .about("A timestamp manipulation command line utility.")
        .arg(
            Arg::with_name("start")
                .help("starting timestamp")
                .required(true),
        )
        .subcommands(vec![add, sub])
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .get_matches();

    if let Some(r) = run(&matches) {
        println!("{}", Into::<String>::into(r));
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn modulus_operator() {
        assert_eq!(3, md!(-57, 60));
        assert_eq!(0, md!(0, 1));
    }

    #[test]
    fn parsing_should_fail() {
        assert!(TimeStamp::from_str("").is_err());
        assert!(TimeStamp::from_str("-123").is_err());
        assert!(TimeStamp::from_str("03:20:10.400").is_err());
        assert!(TimeStamp::from_str("03:20:10,400,200").is_err());
    }

    #[test]
    fn parser_differentials() {
        // basically any combination of ':' and ',' will work
        // as long as there is exactly 4 of them.
        assert!(TimeStamp::from_str("01:01:01:000").is_ok());
        assert!(TimeStamp::from_str("01,01,01,000").is_ok());
        assert!(TimeStamp::from_str("01:01,01:000").is_ok());
    }

    #[test]
    fn parse_from_str() {
        let result = TimeStamp::from_str("00:01:02,400").unwrap();
        assert_eq!(result, TimeStamp([400, 2, 1, 0]));
    }

    #[test]
    fn parse_from_box() {
        let from: Box<[i16]> = Box::new([200, 3, 4, 1]);
        assert!(TimeStamp::try_from(from).is_ok());
    }

    #[test]
    fn equality() {
        let a = TimeStamp::from_str("01:01:01,000");
        let b = TimeStamp::from_str("01:01:01,000");
        assert_eq!(a, b);

        let a = TimeStamp::from_str("01:02:01,000");
        let b = TimeStamp::from_str("01:01:61,000");
        assert_eq!(a, b);
    }

    #[test]
    fn ordering() {
        let a = TimeStamp::from_str("00:01:02,001");
        let b = TimeStamp::from_str("00:01:02,000");
        assert!(a > b && b < a);
    }

    #[test]
    fn into_string() {
        let r = TimeStamp::from_str("03:20:10,400").unwrap();
        assert_eq!(Into::<String>::into(r), String::from("03:20:10,400"))
    }
}
