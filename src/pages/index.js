/**
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 * @format
 */

import React from 'react';
import Layout from '@theme/Layout';
import useBaseUrl from '@docusaurus/useBaseUrl';

export default function Index() {
  return (
    <Layout title="Waterfox Classic">
      <div>
        <div className="splash">
          <div className="content">
            <h1>Waterfox Classic</h1>
            <h2>
              Waterfox Classic is a legacy web browser for older systems and those
              that require use of XPCOM and XUL extensions.
            </h2>
            <h3>
              ⚠️ Waterfox Classic has many unpatched <a href="https://github.com/WaterfoxCo/Waterfox-Classic/wiki/Unpatched-Security-Advisories">security advisories</a>. Use at your own discretion.
            </h3>
              <div>
                <p className="landing-btn landing-btn-left landing-btn-label">
                  Download
                </p>
                <a
                  className="landing-btn landing-btn-middle primary mac-btn"
                  href="https://github.com/WaterfoxCo/Waterfox-Classic/releases/latest">
                  Mac
                </a>
                <a
                  className="landing-btn landing-btn-middle primary linux-btn"
                  href="https://github.com/WaterfoxCo/Waterfox-Classic/releases/latest">
                  Linux
                </a>
                <a
                  className="landing-btn landing-btn-right primary win-btn"
                  href="https://github.com/WaterfoxCo/Waterfox-Classic/releases/latest">
                  Windows
                </a>
              </div>
              <p className="releaseinfo"></p>
            <div className="slideshow">
              <img src={useBaseUrl('img/browser.svg')} className="splashScreen" />
              {/* <img
                src={useBaseUrl('img/layout.png')}
                className="splashScreen"
              />
              <img
                src={useBaseUrl('img/network.png')}
                className="splashScreen"
              />
              <img
                src={useBaseUrl('img/crashreporterplugin.png')}
                className="splashScreen"
              /> */}
            </div>
            <div className="shadow" />
          </div>
        </div>
        <div className="content row">
          <div className="col">
            <h4>Add-ons</h4>
            <h3>Extending Waterfox Classic</h3>
            <p>
              Waterfox Classic is based on an older version of the Gecko platform which
              allows the development of XPCOM and XUL add-ons.
            </p>
          </div>
          <div className="col center">
            <img
              src={useBaseUrl('img/FlipperKit.png')}
              srcSet={`${useBaseUrl('img/FlipperKit.png')} 1x, ${useBaseUrl(
                'img/FlipperKit@2x.png',
              )} 2x`}
            />
          </div>
        </div>
        <div className="content row">
          <div className="col">
            <img
              src={useBaseUrl('img/plugins.png')}
              srcSet={`${useBaseUrl('img/plugins.png')} 1x, ${useBaseUrl(
                'img/plugins@2x.png',
              )} 2x`}
            />
          </div>
          <div className="col">
            <h4>Open Source</h4>
            <h3>Contributing to Waterfox Classic</h3>
            <p>
              Waterfox Classic is open-source
              and MPL2 licensed. This enables you to see and understand how we
              are building Classic, and of course join the community and help
              improve Classic. If you see something missing, please contribute to Classic!
            </p>
            <a
              className="learnmore"
              href="https://github.com/WaterfoxCo/Waterfox-Classic"
              target="_blank">
              Explore the source on GitHub
            </a>
          </div>
        </div>
      </div>
    </Layout>
  );
}
