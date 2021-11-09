/**
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 * @format
 */

const repoUrl = 'https://github.com/WaterfoxCo/Waterfox-Classic';
const siteConfig = {
  title: 'Waterfox Classic',
  tagline: 'The web browser for legacy systems.',
  url: 'https://waterfoxco.github.io/',
  baseUrl: '/waterfox-classic/',
	onBrokenLinks: "ignore",
	onBrokenMarkdownLinks: "warn",
  organizationName: "WaterfoxCo",
  projectName: 'Waterfox-Classic',
  themeConfig: {
    navbar: {
      title: 'Waterfox Classic',
      logo: {
        alt: 'Waterfox Classic Logo',
        src: 'img/logo.svg',
      },
      items: [
        {to: 'https://www.waterfox.net/blog/', label: 'Blog', position: 'right'},
        {
          href: repoUrl,
          position: 'right',
          'aria-label': 'GitHub repository',
          className: 'navbar-github-link',
        },
      ],
    },
    colorMode: {
      // Nothing against dark mode, but our current CSS doesn't have high contrast
      // so it needs some work before being enabled.
      defaultMode: 'light',
      disableSwitch: true,
    },
    footer: {
      style: 'dark',
      links: [
        {
          title: 'Add-ons',
          items: [
            {
              label: 'Add-ons',
              href: 'https://addons.thunderbird.net/en-uS/firefox/',
            },
          ],
        },
        {
          title: 'Legal',
          // Please do not remove the privacy and terms, it's a legal requirement.
          items: [
            {
              label: 'Privacy',
              href: 'https://www.waterfox.net/docs/policies/privacy',
            },
            {
              label: 'Terms',
              href: 'https://www.waterfox.net/docs/policies/terms',
            },
          ],
        },
        {
          title: 'More',
          items: [
            {
              label: 'Twitter',
              href: 'https://twitter.com/Waterfoxproject',
            },
            {
              label: 'GitHub',
              href: repoUrl,
            },
          ],
        },
      ],
      copyright: 'Copyright © ' + new Date().getFullYear() + ' Waterfox Limited.',
      logo: {
        alt: 'Waterfox Logo',
        src: 'img/logo.svg',
      },
    },
/*     algolia: {
        apiKey: '2df980e7ffc95c19552790f7cad32666',
        indexName: 'fbflipper',
        algoliaOptions: {
          hitsPerPage: 5,
        },
      }, */
    prism: {
      additionalLanguages: [
        'groovy',
        'java',
        'kotlin',
        'ruby',
        'swift',
        'objectivec',
      ],
    },
  },
  favicon: 'img/icon.png',
  scripts: [
    'https://buttons.github.io/buttons.js',
    'https://cdnjs.cloudflare.com/ajax/libs/clipboard.js/2.0.0/clipboard.min.js',
    '/js/code-blocks-buttons.js',
  ],
  stylesheets: [],
  // start_config_example
  presets: [
    [
      "@docusaurus/preset-classic",
      {
        docs: false, //Until we add some!
        theme: {
          customCss: require.resolve("./static/css/custom.css"),
        },
      },
    ],
  ],
  // end_config_example
};

module.exports = siteConfig;
